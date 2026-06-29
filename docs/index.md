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
  `Classical.choice`-free. `Slice/Functor.lean` packages it
  categorically as `domFunctor : Over dom ⥤ Type` (reusing the core
  `obj`/`map`) and, via `Functor.toOver`, `functor : Over dom ⥤ Over cod`;
  that module is listed in `GebMeta.classicalAllowedModules` because
  mathlib's `Over` is `Classical.choice`-dependent at the type level.
  `Slice/W.lean` builds the W-type (initial algebra) of a slice
  endofunctor (`dom = cod = I`) on top of mathlib's `PFunctor` W-type.
  The root index `windexRoot` (a tree's root tag) is non-recursive; the
  domain-restriction predicate `WValid` comes from the non-dependent
  W-type eliminator `WType.elim`, which folds an index and a validity
  component together as `windexValid : P.W → WIndex I` (its index
  component agreeing with `windexRoot`). The carrier `W` is the
  admissible trees, with structure map `windex`, mutually-inverse
  constructor and destructor `W.mk`/`W.dest`, and eliminator `W.elim`
  into any slice algebra over `I`. Only the existence half of
  initiality is established (the carrier, its fixed-point structure,
  and the catamorphism `W.elim` with its laws), not uniqueness.
  `Classical.choice`-free.
- `Geb/Mathlib/Data/PFunctor/Presheaf/` — presheaf polynomial functors
  (parametric-right-adjoint functors `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`),
  built as a restriction of `SlicePFunctor`. The per-layer structure
  mirrors the slice pattern: a `…Data` record bundles the operations, a
  `Prop`-valued `…Data.IsFunctorial` record carries the named law
  conditions, and the bundle wraps both. `Presheaf/Basic.lean` is the
  constructive core (`PresheafDomPFunctor`, `PresheafPFunctor`,
  `obj`/`map`, `objPresheaf` assembling the output as a genuine
  presheaf), `Classical.choice`-free. `Presheaf/Functor.lean` packages
  the result as a categorical functor (`domFunctor`, `functor`); that
  module is listed in `GebMeta.classicalAllowedModules`.
