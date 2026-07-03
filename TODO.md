# TODO

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [In progress](#in-progress)
- [Next up](#next-up)
  - [1. Standardise slice and polynomial-diagram terminology](#1-standardise-slice-and-polynomial-diagram-terminology)
  - [2. Presheaf W-types](#2-presheaf-w-types)
  - [3. Categorical wrappers for mathlib's `PFunctor` and `WType`](#3-categorical-wrappers-for-mathlibs-pfunctor-and-wtype)
  - [4. Categorical wrappers for slice and presheaf W-types as initial algebras](#4-categorical-wrappers-for-slice-and-presheaf-w-types-as-initial-algebras)
  - [5. M-types and their categorical wrappers as terminal coalgebras](#5-m-types-and-their-categorical-wrappers-as-terminal-coalgebras)
  - [6. Universal morphisms: limits, colimits, exponentials](#6-universal-morphisms-limits-colimits-exponentials)
  - [7. Free monads](#7-free-monads)
  - [8. Cofree comonads](#8-cofree-comonads)
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

The current stack, each layer expressed as constraints or tags on
the layer below: mathlib `PFunctor` (`Type` endofunctors) → slice
polynomial functors (`Geb/Mathlib/Data/PFunctor/Slice/`) →
presheaf parametric-right-adjoint functors
(`Geb/Mathlib/Data/PFunctor/Presheaf/`). Categorical
interpretations into mathlib's category theory are kept thin to
minimise the `Classical.choice` surface. Slice W-types
(`Slice/W.lean`) exist; the roadmap extends the stack upward.

### 1. Standardise slice and polynomial-diagram terminology

Replace non-standard names and comments with widely-accepted
terms. For a slice (`Over`) object — an object `e` with a
morphism `p : e → c` over a base `c` — standardise on "base
space" for `c`, "total space" for `e`, and "projection" for `p`,
abbreviating to "base object" and "total object" where "space"
reads awkwardly.

Open for that branch's brainstorming: the current sources use
"constraint leg" for the direction-indexing map `s` and "tag leg"
for the shape-indexing map `t`. These name the structure maps of
the polynomial diagram, distinct from the base/total/projection
triple above, so their replacements are a separate decision.
Where multiple standard options exist, the user states a
preference before the term is fixed.

### 2. Presheaf W-types

Define the W-types (initial algebras) of the presheaf polynomial
functors as constraints or tags on the slice polynomial W-types
in `Slice/W.lean`, mirroring how the presheaf functors are
constraints or tags on the slice functors and the slice functors
on mathlib's `PFunctor`. This layers presheaf W-types on mathlib's
`PFunctor.W` through the existing slice layer.

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

### 6. Universal morphisms: limits, colimits, exponentials

Establish the limits, colimits, and exponentials of the slice and
presheaf functors. Layer the slice constructions on mathlib's
`PFunctor` and the presheaf constructions on the slice
constructions. Per the survey, mathlib carries little or none of
this for `PFunctor`, so a base layer of universal morphisms for
mathlib's `PFunctor` is likely required.

### 7. Free monads

Build free monads over the slice and presheaf functors as
constraints or tags on cslib's `PFunctor.FreeM` (the free monad of
a polynomial functor), mirroring the layering of the functors
themselves.

Two definitions of these free monads are to be shown equivalent,
in the most reusable form available: as constraints or tags on
cslib's `PFunctor.FreeM`, and as computed from the slice and
presheaf W-types of items 2 and 4 (themselves constraints or tags
on mathlib's `WType`). Define both and prove them equivalent.

### 8. Cofree comonads

Build cofree comonads over the slice and presheaf functors. If
mathlib and cslib lack a cofree comonad of a polynomial functor,
build the `PFunctor` version first as a base layer. The survey
records cslib's `PFunctor.FreeM` but no cofree-comonad
counterpart; confirm before relying on it.

Two definitions of these cofree comonads are to be shown
equivalent: as constraints or tags on the `PFunctor` version, and
as derived from the slice and presheaf M-types of item 5. Define
both and prove them equivalent.

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
- **Update `Authors:` lines as content authors arrive**: every
  `.lean` file ships with `Authors: The geb-mathlib contributors`.
  When a contributor authors substantive content in a file,
  update that file's `Authors:` line to credit them by name.
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
