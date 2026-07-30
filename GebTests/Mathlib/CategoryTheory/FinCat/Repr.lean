/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Hom2
public import GebTests.Mathlib.CategoryTheory.FinCat.Basic
public meta import Geb.Mathlib.CategoryTheory.FinCat.Repr  -- shake: keep; #guard needs it
public meta import GebTests.Mathlib.CategoryTheory.FinCat.Basic  -- shake: keep; #guard needs it
public meta import GebTests.Mathlib.CategoryTheory.FinCat.Hom2  -- shake: keep; #guard needs it

/-!
# Tests for `Repr`

One assertion per level: a specification, a 1-cell and a 2-cell. The
1-cell is `FinCat.Hom.id walkingIso`, not `idemPoint`: every 1-cell
fixture with `terminalCat` as source has an empty morphism table, and
would leave `FinCat.Hom.instRepr`'s innermost `List.ofFn` unexercised.
`walkingIso` is the source that populates it.

The 2-cell level carries two assertions: `idemCellIdem`, whose source
is `terminalCat`, and `isoIdCell`, whose source is `walkingIso`. At a
one-object source the rendered component vector cannot distinguish an
object index from a component value, so `idemCellIdem` alone would pass
under a `Hom₂.instRepr` body that rendered indices rather than
components; `isoIdCell` has two objects and closes that gap.

## Implementation notes

The two ordinary imports back `isoIdCell`, the one declaration here
outside a `#guard`: it names `FinCat.Hom₂`, `FinCat.Hom.id` and
`walkingIso` directly, and `FinCat.Hom.id` needs no import of its own,
being public from `Hom2`. The three meta imports back the `#guard`s,
each of which crosses a module boundary to a non-`meta` declaration at
evaluation time; the two sets need not coincide, and `lake shake`
settles both.

## Tags

category, functor, natural transformation, finite category, repr,
constructive
-/

@[expose] public section

-- Assertion 1: a specification renders as its object count, its count
-- matrix and its composition table.
#guard reprStr walkingIso ==
  "(2, [[0, 1], [1, 0]], [[[[], []], [[[0]], [[]]]], [[[[]], [[0]]], [[], []]]])"

-- Assertion 2: a 1-cell renders as its object map and its morphism
-- table, exercising the morphism table on `walkingIso`'s identity.
#guard reprStr (FinCat.Hom.id walkingIso) == "([0, 1], [[[], [0]], [[0], []]])"

-- Assertion 3: a 2-cell renders as its component vector.
#guard reprStr idemCellIdem == "[0]"

/-- The identity 2-cell on the identity 1-cell of `walkingIso`. Its
source has two objects, so its rendered component vector discriminates
a component-value rendering from an object-index rendering, which
`idemCellIdem`'s one-object source cannot. -/
def isoIdCell : FinCat.Hom₂ (FinCat.Hom.id walkingIso) (FinCat.Hom.id walkingIso) where
  app := fun i ↦ walkingIso.id i
  natValid := rfl

-- Assertion 4: and at a two-object source, distinguishing a component
-- value from an object index.
#guard reprStr isoIdCell == "[0, 0]"
