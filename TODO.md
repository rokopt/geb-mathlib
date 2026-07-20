# TODO

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [In progress](#in-progress)
- [Next up](#next-up)
  - [1. Decidable-property specializations of the functor definitions](#1-decidable-property-specializations-of-the-functor-definitions)
  - [2. Presheaf W-types — completed](#2-presheaf-w-types--completed)
  - [3. Categorical wrappers for mathlib's `PFunctor` and `WType`](#3-categorical-wrappers-for-mathlibs-pfunctor-and-wtype)
  - [4. Categorical wrappers for slice and presheaf W-types as initial algebras](#4-categorical-wrappers-for-slice-and-presheaf-w-types-as-initial-algebras)
  - [5. M-types and their categorical wrappers as terminal coalgebras](#5-m-types-and-their-categorical-wrappers-as-terminal-coalgebras)
  - [6. Universal morphisms](#6-universal-morphisms)
  - [7. Relative (co)free (co)monads](#7-relative-cofree-comonads)
  - [Complete Theorem 2.4 for `IndRec`](#complete-theorem-24-for-indrec)
  - [Category of `IR` codes](#category-of-ir-codes)
  - [Validate `PresheafPFunctor.functor` as a parametric right adjoint](#validate-presheafpfunctorfunctor-as-a-parametric-right-adjoint)
- [Triggers (do when condition fires)](#triggers-do-when-condition-fires)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Active workstreams, in topological order. Workstreams complete →
removed; content merged into `docs/index.md`.

## In progress

(None — bootstrap complete.)

## Next up

The polynomial-functor roadmap below is a linear sequence of
separate planning–implementation cycles. Each item's full spec
and plan are written only after the prior item's implementation
is complete: the project is too large to fix every earlier
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
minimise the `Classical.choice` surface. Slice W-types
(`Slice/W.lean`) exist; the roadmap extends the stack upward.

### 1. Decidable-property specializations of the functor definitions

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
morphisms (item 6).

### 2. Presheaf W-types — completed

Implemented in `Presheaf/W.lean`; see `docs/index.md`. The presheaf W-type
is the hereditarily-natural subtype of the slice W-type, `ULift`ed to the
functor's value universe, with fixed-point `W.mk`/`W.dest` and the
eliminator `W.elim` (`elim_mk`/`comp_elim`). Existence half of initiality
only; uniqueness and the categorical initial-object wrapper remain item 4.
Item numbers below are retained so their cross-references stay stable.

### 3. Categorical wrappers for mathlib's `PFunctor` and `WType`

Connect mathlib's generic endofunctor algebras to `PFunctor` as a
reusable base layer. Per the survey, mathlib has
`CategoryTheory.Endofunctor.Algebra` with the Lambek isomorphism
but nothing linking it to `PFunctor`. Add files parallel to the
existing directory structure: one wrapping mathlib's `PFunctor` as
an endofunctor with its algebra category, and one wrapping
mathlib's `WType` as the initial algebra of that endofunctor. Then
refactor the existing categorical wrapper of the slice functors
(`Slice/Functor.lean`) to reuse the new `PFunctor` wrapper.

### 4. Categorical wrappers for slice and presheaf W-types as initial algebras

Characterise the slice and presheaf W-types as the initial objects
of the categories of algebras of their functors, reusing the
`PFunctor` and `WType` wrappers of item 3. Build the presheaf
initiality proof on the slice initiality proof, and the slice
proof on the `WType` initiality of item 3.

### 5. M-types and their categorical wrappers as terminal coalgebras

Define the M-types (greatest fixed points) of the slice and
presheaf functors on mathlib's `PFunctor.M`, following mathlib's
standard construction of M-types on W-types, and characterise them
as the terminal coalgebras of their functors. Following the
base-layer-first pattern of items 3 and 4, build a categorical
wrapper for the terminality of mathlib's `PFunctor.M` first,
reusable in the slice and presheaf terminality proofs.

### 6. Universal morphisms

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

### 7. Relative (co)free (co)monads

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
corresponding slice/presheaf W-type (item 4) or M-type (item 5) and
show the definitions equivalent, as in the superseded free-monad and
cofree-comonad items.

### Complete Theorem 2.4 for `IndRec`

Independent of the roadmap sequence above; layered like items 3–4
(constructive core first, thin `Classical.choice`-enabled categorical
wrapper second). The two remaining layers for Theorem 2.4 of
[GhaniNordvallForsbergMalatesta2015] follow.

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

Tests: the propositional computation rule (`IR.rec_mk`) exists;
add a morphism-action test with a propositionally nontrivial
commutation proof (distinct decodings on domain and codomain),
exercising the `FreeCoprodCompDisc.homOfEq` transport in
`IR.interpMorDelta` observably; the current tests exercise the
morphism action only at the algebra level and only along
definitionally trivial transports.

### Category of `IR` codes

Independent of the roadmap sequence above; parallel to
Complete Theorem 2.4 for `IndRec`. The functor laws of
`IR.interpMor` (`IR.interpMor_id`, `IR.interpMor_comp`) that a
natural-transformation notion of code morphism requires are
available. Following Definition 8 and Corollary 2 of
[HancockMcBrideGhaniMalatestaAltenkirch2013], establish the category
of `IR` codes for a fixed input/output index pair: the homset between
two codes, the identity morphism, composition, and the category laws
(identity and associativity).

Establishing the natural-transformation notion (Theorem 3 of
[GhaniNordvallForsbergMalatesta2015]) additionally requires
upgrading the pointwise isomorphisms of Lemma 3 (`IR.interpDeltaIso`)
and Lemma 4 (`IR.interpPrecompIso`) to natural isomorphisms; this
deliverable is not yet scheduled and must be budgeted for.

### Validate `PresheafPFunctor.functor` as a parametric right adjoint

Independent of the roadmap sequence above. Establish the natural
isomorphism confirming that `PresheafPFunctor.functor` is the
parametric right adjoint determined by its generic data
`(T1, E_T)`.

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
