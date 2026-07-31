# TODO

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [In progress](#in-progress)
- [Next up](#next-up)
  - [Removal of guard hash-command](#removal-of-guard-hash-command)
  - [Polynomial functors](#polynomial-functors)
    - [1. Categorical wrappers for slice and presheaf W-types as initial algebras](#1-categorical-wrappers-for-slice-and-presheaf-w-types-as-initial-algebras)
    - [2. M-types and their categorical wrappers as terminal coalgebras](#2-m-types-and-their-categorical-wrappers-as-terminal-coalgebras)
    - [3. Universal morphisms](#3-universal-morphisms)
    - [4. Relative (co)free (co)monads](#4-relative-cofree-comonads)
    - [5. Composition and identity of polynomial functors](#5-composition-and-identity-of-polynomial-functors)
  - [Complexity of the decidable validity checkers](#complexity-of-the-decidable-validity-checkers)
  - [Non-vacuous composition check for `FinCat` 1-cells](#non-vacuous-composition-check-for-fincat-1-cells)
  - [Upstream placement of categorical wrappers](#upstream-placement-of-categorical-wrappers)
  - [Upstream destination of core- and Batteries-targeted content](#upstream-destination-of-core--and-batteries-targeted-content)
  - [Complete Theorem 2.4 for `IndRec`](#complete-theorem-24-for-indrec)
  - [Theorems 2 and 4 for `IR` codes](#theorems-2-and-4-for-ir-codes)
  - [Validate `PresheafPFunctor.functor` as a parametric right adjoint](#validate-presheafpfunctorfunctor-as-a-parametric-right-adjoint)
  - [Exhaustive verification of presheaf PRA laws for finite instances](#exhaustive-verification-of-presheaf-pra-laws-for-finite-instances)
  - [PRA functors over finite-specification base categories](#pra-functors-over-finite-specification-base-categories)
  - [Finite categories as a full subcategory of `Cat`](#finite-categories-as-a-full-subcategory-of-cat)
- [Triggers (do when condition fires)](#triggers-do-when-condition-fires)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Active workstreams, in topological order. Workstreams complete →
removed; content merged into the persistent documentation.

## In progress

(None.)

## Next up

### Removal of guard hash-command

- **`#guards should be removed`: mathlib disallows `#guard`, so we
  should as well; our coding standards are meant to be at least as
  strict as theirs, at least for anything not under `Geb/Internal/`.
  `docs/lean-coding.md` has a reference to uses of `#guard`; it
  should say that we shouldn't use it. One possible exception is
  `AxiomLinter.lean`, which _is_ in `Geb/Internal/` and, as an
  internal test file, might not need to adhere to that mathlib
  convention. We should still make it do so if it can function
  equally well without `#guard`.

### Polynomial functors

The polynomial-functor roadmap below is a partial order of
separate planning–implementation cycles. Items with disjoint file
sets that do not depend on one another may be taken in either
order. Each item's full spec and plan are written only after the
items it depends on are implemented: the project is too large to
fix every earlier
interface on the first attempt, so interface corrections in an
earlier item can invalidate a later item's plan. Each item lives
on its own topic branch and migrates to persistent documentation
under `docs/index.md` on completion.

The current stack, each layer expressed as restrictions or assignments on
the layer below: mathlib `PFunctor` (`Type` endofunctors) → slice
polynomial functors (`Geb/Mathlib/Data/PFunctor/Slice/`) →
presheaf parametric-right-adjoint functors
(`Geb/Mathlib/Data/PFunctor/Presheaf/`). Categorical
interpretations into mathlib's category theory are kept thin to
minimise the `Classical.choice` surface. Slice and presheaf W-types
(`Slice/W.lean`, `Presheaf/W.lean`) exist, with the existence half of
initiality only; the roadmap extends the stack upward.

#### 1. Categorical wrappers for slice and presheaf W-types as initial algebras

Characterise the slice and presheaf W-types as the initial objects
of the categories of algebras of their functors, reusing the
`PFunctor` and `WType` wrappers described under
`Geb/Mathlib/Data/PFunctor/Univariate/` in `docs/index.md`. Build the
presheaf initiality proof on the slice initiality proof, and the slice
proof on the `WType` initiality established there.

#### 2. M-types and their categorical wrappers as terminal coalgebras

Define the M-types (greatest fixed points) of the slice and
presheaf functors on mathlib's `PFunctor.M`, following mathlib's
standard construction of M-types on W-types, and characterise them
as the terminal coalgebras of their functors. Following the
base-layer-first pattern of the `PFunctor` wrappers and item 1,
build a categorical
wrapper for the terminality of mathlib's `PFunctor.M` first,
reusable in the slice and presheaf terminality proofs.

#### 3. Universal morphisms

Establish the universal morphisms of the slice and presheaf functors,
layering the slice constructions on mathlib's `PFunctor` and the
presheaf constructions on the slice constructions. Per the survey,
mathlib carries little or none of this for `PFunctor`, so a base layer
for mathlib's `PFunctor` is likely required. Model formulas for a
different representation, to be adapted, are in
[rokopt/geb `PolyUMorph.lean`](https://github.com/rokopt/geb/blob/main/geb-lean/GebLean/PolyUMorph.lean).

Implement in this order, each step layered across the three forms:

1. Representables (every representable is polynomial).
2. Small coproducts (indexed by any `Type u`): every polynomial is
   then a coproduct of representables; the first part of general
   colimits; includes the initial object (the coproduct over `Empty`).
3. Day convolution: the first part of general limits.
4. Commutativity of coproducts with Day convolution.
5. Small products, as an instantiation of Day convolution.
6. Small parallel products, as an instantiation of Day convolution.
7. Exponential objects.
8. Left Kan extension.
9. Equalizers.
10. All small limits, by instantiating mathlib's construction of
    limits from products and equalizers.
11. Coequalizers.
12. All small colimits, by instantiating mathlib's construction of
    colimits from coproducts and coequalizers.

Following the general definitions, implement the decidable-case
specializations of those universal morphisms with interesting
decidable forms, building on the `PFunctor.Finitary` layer documented
in `docs/index.md`.

#### 4. Relative (co)free (co)monads

Build the relative free monads and relative cofree comonads of the
slice and presheaf functors for all three forms, and prove the
relative universal property. A slice or presheaf functor is an
endofunctor only when its domain and codomain bases coincide, so the
relative notion [AltenkirchChapmanUustalu2015] is the appropriate one
for the general (non-endofunctor) case; the ordinary free monad and
cofree comonad are the `J = id` special case. The formal theory is
[ArkorMcDermott2024]. Model definitions: cslib's `PFunctor` free monad
(`Cslib/Foundations/Data/PFunctor/Free.lean`, the ordinary case) and
[rokopt/geb `RelativeMonad.lean`](https://github.com/rokopt/geb/blob/main/geb-lean/GebLean/Binding/RelativeMonad.lean)
(the relative case, in extension form). The first intended application
is generic syntaxes with binding [AllaisAtkeyChapmanMcBrideMcKinna2021],
which also supplies test material for the relative monads.

Open technical question, resolved when this item is taken up, that
determines implementation order: whether the relative (co)free
(co)monad can be built on top of the ordinary one — as the slice
functors are built on `PFunctor` and the presheaf functors on the
slice functors. The primary constraint is to avoid code duplication;
within that, build the simpler pieces first and the more complex on
top of them when that can be done without duplication. If the relative
version can be built on the ordinary one, do so (simpler-first with
reuse); otherwise build the relative version and define the ordinary
one as its `J = id` specialization — known achievable, the ordinary
case being the discrete degeneration. Relate each construction to the
corresponding slice/presheaf W-type (item 1) or M-type (item 2) and
show the definitions equivalent, as in the superseded free-monad and
cofree-comonad items.

#### 5. Composition and identity of polynomial functors

Establish that the interpretation of mathlib's `PFunctor` carries
`PFunctor.comp` to composition of the corresponding functors, and
supply the identity polynomial functor together with the isomorphism
identifying its interpretation with the identity functor. mathlib
defines `comp`, `comp.mk`, and `comp.get` and states no lemma about
them, so the mutual-inverse laws `comp.get_mk` and `comp.mk_get` are
part of the item.

This is the 1-cell composition of `Cat`, a 2-categorical operation,
not a universal morphism. It is independent of the items above and may
be taken in any order relative to them. Two design points are settled:
the identity polynomial functor is `protected def PFunctor.id`, since
an unprotected `id` shadows `_root_.id` throughout the `PFunctor`
namespace and breaks uses such as `P.map id`; and both isomorphisms
admit an ambient universe beyond the parameters of the functors
involved.

### Complexity of the decidable validity checkers

Prove the complexity bounds conjectured, but not proved, for the
checkers in `Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean` and
`Geb/Mathlib/Data/PFunctor/Presheaf/Decidable.lean` (see
`docs/index.md`). With `n` the number of nodes of the input term, `h`
its height, `k` the branching bound, `κ` the number of objects of `I`,
and `H` the maximal hom-set size, and taking equality in `I`, in
`dom`, and in the presheaf's value types to cost `O(1)`: the four
single-step checks are constant-time in `n`, with node-level factors
`1` for the two fiber predicates, `k` for `Compatible`, and `κ²Hk` for
`IsNatural`; `WValid` runs in `O(k · n)`, a single fold with an
`O(1)` accumulator; and `IsHereditarilyNatural` runs in
`O(κ²Hk · n · h)`, worst case `O(n²)`, because each node's local
condition is an equation between a subtree and the root-restriction
of a sibling, whose decision cost is linear in subtree size. All six
are polynomial time, and the functor's data enters as multiplicative
constants rather than as a change of complexity class. Upper bounds
only: a `Bool` fold short-circuits, so no matching lower bound is
claimed on rejecting inputs.

A sharing or hash-consing representation would reduce
`IsHereditarilyNatural`'s checker to linear time, each subtree
comparison becoming a pointer comparison; building that
representation is out of scope for this item.

[Leivant1999], [DalLagoMartiniZorzi2010], and [AvanziniDalLago2018]
place the checkers' complexity: every recursion here is a
non-dependent fold at a first-order carrier, the regime those results
place in first-order polynomial time, as against the higher-order and
word-algebra regimes in which they identify an elementary or
exponential jump.

`FinCat.assocCheck`
(`Geb/Mathlib/CategoryTheory/FinCat/Basic.lean`) is in scope for the
same treatment. It enumerates `Θ(objCount⁴) + O(M³)` tuples, where `M`
is the total non-identity morphism count: four object quantifiers stand
outside the three morphism quantifiers, so a discrete category on `n`
objects costs `n⁴` iterations even at `M = 0`. Reserving an index for
each identity keeps the identity cases out of the quantifier entirely,
the identity laws holding by construction, so the morphism factor is
the non-identity count rather than the total. As above this is an upper
bound only, the `Bool` conjunction short-circuiting on rejection.

### Non-vacuous composition check for `FinCat` 1-cells

Give `GebTests/Mathlib/CategoryTheory/FinCat/Hom.lean` a 1-cell fixture
whose composition check is not vacuous. `FinCat.Hom.compCheckOf`
quantifies over pairs of composable client morphisms of the source, and
no fixture's source has such a pair: the sources are `terminalCat`,
which has no client morphisms, and `walkingArrow`, whose one client
morphism composes with nothing. So `arrowPointSrc_compCheck` and every
`compValid` field there holds over an empty range.

`idemMonoid` is the only fixture whose source qualifies, its idempotent
composing with itself, so a 1-cell out of `idemMonoid` into
`terminalCat` is the cheapest fixture that makes the quantifier bite.
That alone does not settle the item: every morphism map into
`terminalCat` satisfies the equation, so a fixture the check rejects
needs a target whose composition discriminates, and both candidate
morphism maps out of `idemMonoid` into itself are functorial. The
other two checkers have their rejecting instances already —
`badComp_assocCheck_eq_false` for `FinCat.assocCheckOf` and
`arrowIdem_natCheckOf_id_eq_false` for `FinCat.Hom₂.natCheckOf`.

### Upstream placement of categorical wrappers

Settle where the categorical wrappers under `Geb/Mathlib/Data/` belong
upstream. No file under mathlib's `Mathlib/Data/` imports
`Mathlib.CategoryTheory.*`; mathlib packages category-theoretic
material under `Mathlib/Algebra/Category/` and
`Mathlib/CategoryTheory/`. In scope is every file under
`Geb/Mathlib/Data/` that directly imports `Mathlib.CategoryTheory.*`
or `Geb.Mathlib.CategoryTheory.*`, the latter because it extracts to
the former: currently `PFunctor/Slice/Functor.lean`,
`PFunctor/Presheaf/Basic.lean`, `PFunctor/Presheaf/Functor.lean`,
`PFunctor/Univariate/Functor.lean`, `PFunctor/Univariate/W.lean`,
`PFunctor/Univariate/Initial.lean`, `PFunctor/IndRec/Basic.lean`, and
`PFunctor/IndRec/Naturality.lean`. Files importing those transitively —
`PFunctor/Presheaf/W.lean`, the rest of the `IndRec` family — follow
whatever placement is settled for them. Scoping the item by that
criterion
rather than by a module list keeps it from being settled
incompletely.

### Upstream destination of core- and Batteries-targeted content

Settle where content under `Geb/Mathlib/` whose upstream target is
Lean core or Batteries rather than mathlib4 belongs. Such content
exists because `docs/rules/upstream-eligible.md` § Subtree import
rules restricts `Geb/Mathlib/` modules to `Mathlib.*`, `Batteries.*`
and `Geb.Mathlib.*` imports: a dependency of a `Geb/Mathlib/` module
cannot live in `Geb/Internal/`, so a module restating core or
Batteries API sits under `Geb/Mathlib/` while its upstream is neither
mathlib4 nor CSLib. In scope is every module under `Geb/Mathlib/`, and
every `GebTests/Mathlib/` parallel, whose declarations restate or
replace declarations of Lean core or Batteries rather than of mathlib:
currently `Geb/Mathlib/Data/Vector/OfFn.lean` and
`Geb/Mathlib/Data/UnionFind/OfEdges.lean`, and their test parallels.
The criterion does not literally reach `OfEdges.lean`, whose
declarations extend a Batteries type with new statements rather than
restating or replacing existing ones; it is listed here because this
item's subject — content under `Geb/Mathlib/` whose upstream target is
not mathlib4 — is where such a module belongs. Reconciling the
criterion's wording with that subject is a separate concern, on its
own branch.
Scoping the item by that criterion rather than by a module list keeps
it from being settled incompletely; the criterion does not reach
`Geb/Mathlib/Data/Vector/NodupEquivFin.lean`, whose statement is an
`Equiv` and so has no core or Batteries home.

`scripts/extract-pr.sh` is the enforcer: its `Geb/Mathlib/*` arm maps
unconditionally to `Mathlib/` and its `GebTests/Mathlib/*` arm to
`MathlibTest/`, so a core-targeted module extracts to the wrong
upstream silently. Changing either mapping waits on this item's
outcome.

### Complete Theorem 2.4 for `IndRec`

Layered like the polynomial-functor code (constructive core first, thin
`Classical.choice`-enabled categorical wrapper second). The two remaining
layers for Theorem 2.4 of [GhaniNordvallForsbergMalatesta2015] follow.

In the existing constructive files, without `Classical.choice`,
remaining: the uniqueness properties of `IR.elim` and `IR.rec` as
algebra morphisms, constructively stated (the Theorem 3 development
does not need this item).

In a separate sibling file wrapping the constructive proofs in
mathlib `Category`/`Functor` interfaces (pretty much everything
involving mathlib's `Category` pulls in `Classical.choice`, so the
wrapper is kept thin, following `Slice/Functor.lean` and
`Presheaf/Functor.lean`):

1. `FreeCoprodCompDisc` as a `Category` and the interpretation of a
   code as a `Functor`.
2. The initiality of `IR` in the category of algebras (mathlib's
   `CategoryTheory.Endofunctor.Algebra`), wrapping the constructive
   uniqueness proofs.

### Theorems 2 and 4 for `IR` codes

Parallel to "Complete Theorem 2.4 for `IndRec`", and building on the
category of `IR` codes in `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`
(see `docs/index.md`). Two results of
[HancockMcBrideGhaniMalatestaAltenkirch2013] remain: Theorem 2,
the left-Kan-extension characterization of the `δ`-code
interpretation, and Theorem 4, the equivalence with dependent
polynomial functors.

### Validate `PresheafPFunctor.functor` as a parametric right adjoint

Establish the natural isomorphism confirming that `PresheafPFunctor.functor`
is the parametric right adjoint determined by its generic data `(T1, E_T)`.

### Exhaustive verification of presheaf PRA laws for finite instances

The `FinitePresheafPFunctor` structure bundles `FinEnum J` alongside the
domain finiteness. With both index categories finite, the functor laws
(`ShapeRestrId`, `ShapeRestrComp`, `ReindexNaturality`, `ReindexId`,
`ReindexComp`, and the domain-side `DirectionRestrId`,
`DirectionRestrComp`) are exhaustively verifiable by enumeration: each
law quantifies over finitely many objects, morphisms, shapes, and
directions, and the equalities are decidable (shapes and directions
have `DecidableEq` from the bundled `FinEnum` evidence). A `decide`-
based test harness can confirm that a concrete `FinitePresheafPFunctor`
satisfies all laws without manual proof, turning the law fields from
trusted input into checked input. The laws quantifying over
`J`-morphisms additionally need finite `J`-hom-sets, which the structure
does not currently bundle: a `finEnumHomJ` field is added by the commit
that first consumes it. This is a testing/verification concern (not a
new decidability instance) and is distinct from the decidability of
fiber membership already implemented.

### PRA functors over finite-specification base categories

Instantiate the presheaf parametric-right-adjoint functors of
`Geb/Mathlib/Data/PFunctor/Presheaf/` at base categories presented by
`FinCat` specifications (`Geb/Mathlib/CategoryTheory/FinCat/`), derive
decidable equality on their W-types from the specification's own, and
specify the natural transformations among the resulting functors.

This is the consumer that justifies the functor, 2-cell, `Bicategory`
and `DecidableEq`/`Repr` layers of the `FinCat` workstream under
CONTRIBUTING § Code is cost. Without it those layers have no in-tree
consumer: the comparison with `Cat` below is the only other one and is
itself deferred.

It also supplies what § Exhaustive verification of presheaf PRA laws
for finite instances records as missing. That entry notes that the laws
quantifying over `J`-morphisms need finite `J`-hom-sets, which
`FinitePresheafPFunctor` does not bundle, and anticipates a
`finEnumHomJ` field. A `FinCat` specification carries finite hom-sets
with decidable equality by construction, so the field may be
discharged from a specification rather than added.

One interface constraint carries over. `FinitePresheafPFunctor` bundles
`FinEnum J`, and the `FinCat` workstream establishes by measurement
that mathlib's only `FinEnum (Fin n)` instance, `FinEnum.fin`, depends
on `Classical.choice`, as does `ULift.instFinEnum` over it. Supplying
that field from a `FinCat` specification choice-free therefore needs a
`FinEnum` built directly as a cardinality with `Equiv.refl`, which
competes with `FinEnum.fin` at the same head symbol and so requires the
explicit-supply mitigation `Geb/Mathlib/Data/FinEnum.lean` documents.
The `FinCat` workstream declines that trade, having no need of
`FinEnum`; this item does need it and should price it.

Depends on the `FinCat` workstream.

### Finite categories as a full subcategory of `Cat`

Compare the `FinCat` specifications with the finite categories among
mathlib's, comprising:

- the object property on `Cat.{v, u}` selecting the categories with
  finitely many objects and finitely many morphisms in each hom-set,
  stated as a `Prop` in the shape of
  `CategoryTheory.CountableCategory`. mathlib has no such property:
  `Mathlib/CategoryTheory/Cat/` contains no `ObjectProperty` file, and
  `CategoryTheory.FinCategory` requires `SmallCategory` and so does not
  express it at independent universe levels;
- the 2-functor from `FinCat` to `Cat.{v, u}` extending
  `FinCat.Hom.toFunctor`;
- the proof that it is an equivalence onto that full subcategory.

Two observations from the `FinCat` workstream. Essential surjectivity
chooses `Obj ≃ Fin n` and a bijection on each hom-set, so it depends on
`Fintype.equivFin` and is classical; and because the chosen map on
objects is a bijection, the result is an isomorphism in `Cat` rather
than only an equivalence, as
`Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean` obtains for its
own comparison. The hom-set bijections must be chosen to carry each
identity to the index `FinCat` reserves for it, which is a constraint
that workstream's conventions impose on this one.

Deferred rather than scheduled: this item is the least predictable of
the three that the `FinCat` brainstorming identified, and it is the one
most likely to force revision of `FinCat`'s identity convention or hom
encoding, so it is taken after that workstream's interface has been
exercised by the PRA item above.

Depends on the `FinCat` workstream.

## Triggers (do when condition fires)

- **Choice-free bound for `Fin.divNat` in Batteries**:
  `Geb/Mathlib/Data/Fin/Basic.lean` exists because Batteries'
  `Fin.divNat` proves its bound through `Nat.div_lt_of_lt_mul`,
  which depends on `Classical.choice`, and the two round trips
  stated over `Fin.divNat` inherit that dependence; `Fin.modNat`
  and `Fin.mkDivMod` depend on no axiom outside `propext`. A
  choice-free bound upstream removes the reason for the module.
  Trigger: Batteries admits such a bound, at which point
  `Geb/Mathlib/Data/Fin/Basic.lean` and its test parallel are
  deleted and `Geb/Mathlib/Logic/Equiv/Fin/Basic.lean` is restated
  over `Fin.divNat`, `Fin.modNat` and `Fin.mkDivMod`.
- **`lake shake --keep-implied` versus mathlib CI's plain
  `lake shake`**: a repo-wide decision, on a separate branch, on
  whether to drop `--keep-implied` from `scripts/pre-push.sh:42`
  and minimise imports across the affected files, or to record why
  the project diverges from mathlib CI here.
  `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean` imports
  `Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts`,
  which is transitively supplied by the next import,
  `…LimitsOfProductsAndEqualizers`; `--keep-implied` keeps this
  import out of `scripts/pre-push.sh`'s `lake shake` report, but
  without that flag, `lake shake` reports it as removable, and
  reports the same pattern across the tree:
  `lake shake --add-public --keep-prefix Geb GebTests` reports
  14 `Geb/Mathlib/` files and 5 `GebTests` ones, exiting 1.
  mathlib CI runs `lake shake` without
  `--keep-implied`, and `CONTRIBUTING.md` § Floodgate test commits
  the repo to shipping `Geb/Mathlib/` PRs with no source-code
  changes.
- **Slice polynomial functor natural isomorphism**: when a
  constructive (computable) `Type`-is-locally-cartesian-closed
  structure is available, in mathlib or built here, establish the
  natural isomorphism between `SlicePFunctor.functor` and the
  categorical composite `Σ_t ∘ Π_f ∘ Δ_s`.
- **Adopt `leanprover-community/upstreaming-dashboard-action`**:
  when we judge we have enough novel and interesting content that
  members of the mathlib community would likely want to be made
  aware of the project — a standing question, revisited as content
  grows. Then add the action to CI plus a Pages-published
  dashboard following FLT's pattern.
- **`downstream-reports` registration**: a manual periodic
  checkpoint by the user. Trigger: "do we have enough substantive
  content that registration would be informative for the
  community, given the daily Zulip notification cost?" The pipeline
  and its trigger are described in `docs/process.md` § LKG/FKB
  pipeline.
- **Verso adoption** (three scopes with distinct gates; doc-gen4
  and Verso are complementary, not alternatives — doc-gen4
  generates the API reference, Verso authors hand-written prose):
  1. Docstrings in `.lean` files: gated on doc-gen4 gaining
     Verso-aware rendering and mathlib migrating to Verso;
     contraindicated for `Geb/Mathlib/` and `Geb/Cslib/` until
     both hold (Verso-markup docstrings would read as foreign to
     mathlib reviewers and would not render on the doc-gen4 site).
  2. Persistent prose (`docs/`, a future Geb-language exposition):
     gated on the prose growing substantial and describing stable,
     existing code. `CONTRIBUTING.md`, `AGENTS.md`, `CLAUDE.md`,
     `docs/process.md`, and `docs/rules/*` remain Markdown
     regardless (GitHub rendering, tool and `@import` consumption,
     markdownlint, doctoc).
  3. Transient design docs on feature branches: no external gate;
     candidate for a local-only Verso build to evaluate authoring
     ergonomics and type-checking of embedded Lean.

  Currently using Markdown rendered by doc-gen4. A local pilot
  (2026-07-02) validated the mechanism: Verso and mathlib coexist in
  one lake project at v4.32.0-rc1, embedded Lean type-checks (a
  mismatch fails the build with a locatable error), and
  within-document references resolve. Two follow-up workstreams, each
  its own spec/plan cycle when taken up:
  - Persistent Geb-language exposition seed chapter in Verso
    (scope 2), once exposition-worthy prose exists.
  - Verso for transient feature-branch design docs (scope 3); a
    change to the current Markdown-based brainstorming and
    writing-plans flow, so it needs its own scoping.
- **Project-specific `geb-development` skill**: when recurring
  patterns accumulate that fit neither `CONTRIBUTING.md`,
  `AGENTS.md`, `CLAUDE.md`, `docs/process.md`,
  `docs/rules/*.md`, nor existing `.claude/rules/*.md`. Default
  is to wait for friction.
- **Author `.github/PULL_REQUEST_TEMPLATE/` for our repo**:
  trigger when the first PR against our own repo is opened (most
  likely the bump-PR cron).
- **Curated `notes` / `journal` directory**: trigger if recurring
  ad-hoc explorations accumulate that don't fit `docs/`.
- **Migrate `update.yml` from `GITHUB_TOKEN` to a PAT**: trigger
  if the manual close-and-reopen-to-fire-CI overhead on cron-
  created bump-PRs becomes burdensome.
- **Reconcile test-module import visibility**:
  `GebTests/` modules disagree on whether to `public import` the
  module under test: most do, a minority use plain `import`;
  `GebTests/Internal/`'s
  `public meta import` lines are in the same category. Import
  visibility changes what a module re-exports, so it is deferred.
  Trigger: the next branch that revises the test modules'
  interfaces.
- **Decide a test-declaration privacy discipline**: test modules
  mix `private` and public declarations with no uniform rule;
  the IndRec test's type-valued definitions must stay `@[expose]`
  public for cross-module compilation, so blanket privatization
  is not obviously desirable. Privacy changes module-interface
  visibility, so it is deferred. Trigger: the next branch that
  revises the test modules' interfaces.
- **Add `ext_iff` companions**: mathlib's naming guide
  (§ Extensionality) prescribes bidirectional
  `f = g ↔ ∀ x, f x = g x` companions alongside `ext` lemmas;
  none exist for `GrothendieckOp.hom_ext`,
  `CoGrothendieck.hom_ext`, or `IR.ext` (`IR.snd_eq_of_eq` is a
  converse but is not packaged as `ext_iff`). Adding them alters
  the theorem-set, so it is deferred. Trigger: the next branch
  that revises these interfaces.
- **Extract a shared presheaf test-fixtures module**: the
  `presheafWitness : PresheafPFunctor (Fin 2) (Fin 2)` fixture is
  duplicated in `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`
  and `.../Presheaf/W.lean` because the `Basic` test module has no
  `public section`. Trigger when a third consumer appears: introduce a
  `public`-exported `GebTests/Mathlib/Data/PFunctor/Presheaf/Fixtures.lean`
  and import it from each. The condition has been met:
  `.../Presheaf/Decidable.lean` re-declares the same fixture data as a
  third consumer. Take the extraction together with the two items
  above (test-module import visibility, test-declaration privacy
  discipline); the extraction entails both, since the fixtures module
  can only be shared by making the currently-private fixture data
  public and importing it from every consumer.
- **Choice-free `Array.ofFn` lemmas**: when an upstream submission
  touching root `Vector`'s `ofFn` API is prepared, give
  `Array.getElem_ofFn_go` (`Init/Data/Array/Lemmas.lean`) a
  choice-free proof in Lean core, from which `Array.getElem_ofFn`,
  `Array.toList_ofFn`, `List.toArray_ofFn`, `Vector.getElem_ofFn`,
  `Vector.ofFn_getElem`, `Vector.getElem_range` and
  `Vector.getElem_finRange` all follow, retiring `Vector.ofFnC` and
  its round trips. It does not retire the `get`/`getElem` bridge in
  the same module: core states no `Vector.get_eq_getElem`, and a
  repaired core lemma is still in `getElem` form. The bridge goes only
  if the direct `Batteries.Data.Vector.Lemmas` import is taken at the
  same time, which the repair would make safe by de-tainting
  Batteries' `get_ofFn` and `get_range`; that is a second decision,
  not a consequence of this one. This is a Lean core submission, not a
  mathlib one, and it does not reach
  `Geb/Mathlib/Data/Vector/NodupEquivFin.lean`, whose statement is an
  `Equiv` and so has no core or Batteries home.
- **Choice-free `Skeletal FinSetSkel`**: when a use for it arises
  outside an allowlisted module, prove it directly rather than
  transporting it along the isomorphism to `FintypeCat.Skeleton`. That
  needs a choice-free pigeonhole, mathlib's `Fin.equiv_iff_eq`,
  `Fintype.card_congr` and `Fintype.card_fin` all depending on
  `Classical.choice`. Its consumers are the wrapper and the one
  allowlisted test module that identifies a pushout, so no such
  use has arisen.
- **mathlib-to-Batteries dependency edge**: whether mathlib accepts a
  `Mathlib/`-to-`Batteries/` dependency edge is a maintainer
  judgement — no `Mathlib.*` module references `UnionFind` — and
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`, the
  mathlib-targeted consumer of the union-find layer, needs one to
  extract. (`Geb/Mathlib/Data/UnionFind/OfEdges.lean` itself does
  not: its own upstream target is Batteries.)
  Trigger: the preparation of that module's upstream submission,
  which outlives the FinSetSkel development.
- **Check the leakage prefix in an import line's comment tail**:
  `scripts/lint-imports.sh` Rule 2 exempts a whole import line from
  the self-prefix check, so a self-prefix in a trailing comment on an
  import line passes clean — verified by adding
  `public import Geb.Mathlib.Bar  -- see Geb.Mathlib.Baz` under
  `GebTests/Mathlib/`. Not a regression: the rule has always
  exempted whole lines. The fix direction is to exempt the import
  path alone and apply the prefix check to the line's comment tail.
  Trigger: the next branch that revises `scripts/lint-imports.sh`.
- **Repo-relative paths in upstream-eligible docstrings**: docstrings
  under `Geb/Mathlib/` name paths that carry no meaning for a mathlib
  reviewer, and `scripts/extract-pr.sh` rewrites import lines only, so
  such prose survives extraction unchanged. Instances include the module
  path in `Geb/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean` and
  the same pattern in `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`.
  Repo-wide, so no one workstream's to fix. Trigger: a repo-wide pass
  over upstream-eligible docstrings, on its own branch.
  Workstream labels were a second instance of this and are gone: a
  workstream is a transient concept whose name is arbitrary, so it
  cannot be referred to from persistent code or documentation at all.
  `TODO.md` is where workstreams are named, being the roadmap that
  defines them.
- **`scripts/extract-pr.sh` does not rewrite `meta import` lines**: its
  rewrite is anchored to `^(public import|import)`, so a
  `public meta import` of a self-prefixed sibling is emitted with the
  `Geb.Mathlib.` prefix intact and the extracted file does not compile.
  The two such lines are
  `GebTests/Mathlib/Data/UnionFind/OfEdges.lean` and
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`, where the
  `#guard` assertions need the module under test available to meta
  code. This is the rewriter's counterpart to the `lint-imports.sh`
  item above: both enumerate import forms and both predate the module
  system's `meta` forms. Trigger: the next branch that revises
  `scripts/extract-pr.sh`, or the first extraction of either module.
- **Verify the attested textbook locators**: three locators are recorded
  from secondary attestation and none is verified against its primary
  source. [nLabSkeletalCategory] attests Mac Lane, _Categories for the
  Working Mathematician_ (1971), p. 91 and Riehl, _Category Theory in
  Context_ (2017), p. 34 for the skeleton of a category;
  [nLabFinSet] attests Johnstone, _Sketches of an Elephant_, example 2.1.2
  for the category of finite sets being an elementary topos. Attestation by
  a secondary source is not verification, on the [Pare1974] precedent.
  Trigger: the acquisition of any of the three primary sources, which
  discharges that locator and leaves the entry standing for the others.
- **Reconcile `## Main statements` across the test modules**:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean` carries
  the section, and its siblings do not although each declares named
  theorems. `docs/rules/lean-coding.md` § Documentation requires a section
  when it has content. Trigger: the next occasion to revise those modules.
