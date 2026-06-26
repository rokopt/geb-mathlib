# geb-mathlib documentation

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Directory structure](#directory-structure)
- [Implemented content](#implemented-content)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Directory structure

The repository is laid out narrow-and-deep, with one indexing
`.lean` file per directory.

- `Geb/` — root namespace, split between upstream-eligible and
  downstream-only content.
  - `Geb/Mathlib/` — content authored in mathlib's style and
    intended for eventual upstream extraction to mathlib4;
    imports from `Mathlib.*` and `Geb.Mathlib.*` only.
  - `Geb/Cslib/` — content authored in CSLib's style and
    intended for eventual upstream extraction to CSLib;
    imports from `Mathlib.*`, `Cslib.*`, and `Geb.Cslib.*`
    only.
  - `Geb/Internal/` — content not intended for upstream
    extraction; may import from `Mathlib.*`, `Cslib.*`,
    `Geb.Mathlib.*`, `Geb.Cslib.*`, or `Geb.Internal.*`.
- `GebTests/` — test library mirroring `Geb/`'s structure, with
  `GebTests/Mathlib/`, `GebTests/Cslib/`, and
  `GebTests/Internal/` subdirectories.

The directory split denotes upstream eligibility; the
import-direction rules above are enforced by
`scripts/lint-imports.sh` and corresponding CI.

## Implemented content

- `Geb/Mathlib/Data/PFunctor/Slice/` — slice polynomial functors on
  `Type`. Given a `PFunctor` with a constraint leg `s : Idx → dom` and
  a tag leg `t : A → cod`, a restriction of the `PFunctor`
  interpretation defines a functor `Type/dom → Type/cod`.
  `Slice/Basic.lean` is the constructive core (`SliceDomPFunctor`,
  `SlicePFunctor`, `Compatible`, `obj`/`map` with functoriality),
  `Classical.choice`-free. `Slice/Functor.lean` packages it as
  `CategoryTheory.Functor (Over dom) (Over cod)` (`domFunctor`,
  `functor`) via `Functor.toOver`; that module is listed in
  `GebMeta.classicalAllowedModules` because mathlib's `Over` is
  `Classical.choice`-dependent at the type level. A natural
  isomorphism to the categorical composite `Σ_t ∘ Π_f ∘ Δ_s` is a
  planned follow-on increment.
