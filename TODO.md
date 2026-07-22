# TODO

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [In progress](#in-progress)
- [Next up](#next-up)
  - [Polynomial functors](#polynomial-functors)
    - [1. Decidable-property specializations of the functor definitions](#1-decidable-property-specializations-of-the-functor-definitions)
    - [2. Categorical wrappers for slice and presheaf W-types as initial algebras](#2-categorical-wrappers-for-slice-and-presheaf-w-types-as-initial-algebras)
    - [3. M-types and their categorical wrappers as terminal coalgebras](#3-m-types-and-their-categorical-wrappers-as-terminal-coalgebras)
    - [4. Universal morphisms](#4-universal-morphisms)
    - [5. Relative (co)free (co)monads](#5-relative-cofree-comonads)
    - [6. Composition and identity of polynomial functors](#6-composition-and-identity-of-polynomial-functors)
  - [Upstream placement of categorical wrappers](#upstream-placement-of-categorical-wrappers)
  - [Complete Theorem 2.4 for `IndRec`](#complete-theorem-24-for-indrec)
  - [Theorems 2 and 4 for `IR` codes](#theorems-2-and-4-for-ir-codes)
  - [Validate `PresheafPFunctor.functor` as a parametric right adjoint](#validate-presheafpfunctorfunctor-as-a-parametric-right-adjoint)
- [Triggers (do when condition fires)](#triggers-do-when-condition-fires)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Active workstreams, in topological order. Workstreams complete →
removed; content merged into `docs/index.md`.

## In progress

(None.)

## Next up

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

#### 1. Decidable-property specializations of the functor definitions

The slice and presheaf functors are specializations of mathlib's
`PFunctor`: a restriction to a domain by a compatibility property on
the direction-input map, together with a shape-output map assigning
each shape a codomain index. Add explicit specializations for the case
where the compatibility property is decidable (typically the finitary
case; the exact conditions are settled when this item is taken up).
This specializes the functor definitions directly, so it depends only
on the existing definitions and precedes the constructions built on
them; the decidable functors are then available downstream, in
particular for the decidable-case specializations of the universal
morphisms (item 4).

#### 2. Categorical wrappers for slice and presheaf W-types as initial algebras

Characterise the slice and presheaf W-types as the initial objects
of the categories of algebras of their functors, reusing the
`PFunctor` and `WType` wrappers described under
`Geb/Mathlib/Data/PFunctor/Univariate/` in `docs/index.md`. Build the
presheaf initiality proof on the slice initiality proof, and the slice
proof on the `WType` initiality established there.

#### 3. M-types and their categorical wrappers as terminal coalgebras

Define the M-types (greatest fixed points) of the slice and
presheaf functors on mathlib's `PFunctor.M`, following mathlib's
standard construction of M-types on W-types, and characterise them
as the terminal coalgebras of their functors. Following the
base-layer-first pattern of the `PFunctor` wrappers and item 2,
build a categorical
wrapper for the terminality of mathlib's `PFunctor.M` first,
reusable in the slice and presheaf terminality proofs.

#### 4. Universal morphisms

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
specializations (item 1) of those universal morphisms with interesting
decidable forms.

#### 5. Relative (co)free (co)monads

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
corresponding slice/presheaf W-type (item 2) or M-type (item 3) and
show the definitions equivalent, as in the superseded free-monad and
cofree-comonad items.

#### 6. Composition and identity of polynomial functors

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

## Triggers (do when condition fires)

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
  `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean` uses
  `public import` for its module-under-test while every sibling
  test module uses plain `import`; `GebTests/Internal/`'s
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
  and import it from each.
