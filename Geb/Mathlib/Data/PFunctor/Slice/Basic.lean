/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Slice polynomial functors on `Type` (constructive core)

A `PFunctor` is the middle leg of a Gambino–Hyland polynomial diagram
`dom ◀ s ─ Idx ─ fst ▶ A ─ t ▶ cod`. Adding `s : Idx → dom` and
`t : A → cod` yields a polynomial functor `Type/dom → Type/cod`,
defined as a restriction of the interpretation `P.Obj X = Σ a, B a → X`
to `s`-compatible position assignments, tagged by `t`.

This file is the constructive core: the structures, the compatibility
predicate, the curried constructor, and the object/morphism maps with
their functoriality stated as plain equalities. It names no `Over` and
no `CategoryTheory.Functor`, so it is `Classical.choice`-free. The
categorical packaging is in the sibling `Slice.Functor` module.

## Main definitions

* `SliceDomPFunctor`, `SlicePFunctor` — the structures.
* `SliceDomPFunctor.Compatible` — the position-compatibility predicate.
* `SliceDomPFunctor.obj` / `map` — the domain-restricted functor's
  object and morphism maps; `map_id` / `map_comp` its functoriality.

## Implementation notes

`obj` is a subtype of `PFunctor.Obj`; `map` is `PFunctor.map`
restricted; functoriality reuses `LawfulFunctor (PFunctor.Obj _)`.
`obj`, `map`, `ofCurried`, and `sCurried` are `@[expose]` so the
wrapper and tests can unfold them across the module boundary.

## References

* N. Gambino and M. Hyland, *Wellfounded trees and dependent
  polynomial functors*, TYPES 2003.
* J. Kock, *Polynomial functors and polynomial monads*.

## Tags

polynomial functor, dependent polynomial functor, slice category,
container, PFunctor
-/

public section

universe uA uB uD uC uX

set_option linter.checkUnivs false in
/-- A polynomial functor with a constraint leg `s` assigning each
position (an element of `PFunctor.Idx`) a `dom`-index. -/
@[nolint checkUnivs]
structure SliceDomPFunctor (dom : Type uD) : Type (max (uA + 1) (uB + 1) uD)
    extends PFunctor.{uA, uB} where
  /-- The constraint leg: each position is assigned a `dom`-index. -/
  s : toPFunctor.Idx → dom

set_option linter.checkUnivs false in
/-- A `SliceDomPFunctor` with a tag leg `t` assigning each shape a
`cod`-index. -/
@[nolint checkUnivs]
structure SlicePFunctor (dom : Type uD) (cod : Type uC) : Type (max (uA + 1) (uB + 1) uC uD)
    extends SliceDomPFunctor.{uA, uB, uD} dom where
  /-- The tag leg: each shape is assigned a `cod`-index. -/
  t : toPFunctor.A → cod

attribute [ext] SliceDomPFunctor SlicePFunctor
