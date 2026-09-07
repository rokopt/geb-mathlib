/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.Finite.W
import Geb.Prototypes.PresheafUniverse.Basic

/-!
# Tests for the universe endofunctor on presheaves over the walking arrow

Reduction tests for the shapes, directions, and restriction data of the
prototype universe endofunctor, and resolution tests for the decidability
instances its finiteness evidence supplies.

## Tags

prototype, presheaf, universe, walking arrow, reduction test
-/

set_option linter.privateModule false

open CategoryTheory GebProto.PresheafUniverse

/-! ## The shapes and their arities -/

-- The code shapes lie over the code object and the term shapes over the term
-- object.
example : qShp .base = 0 := by decide
example : qShp .sigma = 0 := by decide
example : qShp .pi = 0 := by decide
example : qShp (.lit true) = 1 := by decide
example : qShp .pair = 1 := by decide

-- A `pair`'s term directions lie over the term object and its code directions
-- over the code object.
example : rDir .pair (.tm false) = 1 := by decide
example : rDir .pair (.ty false) = 0 := by decide

-- The type of a term shape is its code shape, and the code shapes are their
-- own.
example : codeShp (.lit true) = .base := by decide
example : codeShp .pair = .sigma := by decide
example : codeShp .sigma = .sigma := by decide

-- The code direction of a `pair`'s term direction is the code direction with
-- the same component index: the direction-level statement that a component's
-- type sits at the matching code slot.
example : codeDir .pair (.tm true) = .ty true := by decide

-- The `sigma` subcode directions reindex to the `pair` code directions.
example : reindexDir .pair true = .ty true := by decide

/-- The number of shapes the prototype has, read off the `FinEnum` evidence. -/
def shapeCard : Nat := finEnumShp.card

example : shapeCard = 6 := rfl

/-! ## Resolution tests -/

/-- The fiber-membership decision procedure is reachable for the prototype's
finiteness bundle. Named rather than stated as an `example` so that `lake shake`
sees the import: a declaration used only in an `example` leaves no constant in
the olean. -/
def decidableMemWUniverse (j : Fin 2) (w : universeFunctor.toPFunctor.W) :
    Decidable (universeFunctor.MemW j w) :=
  FinitePresheafPFunctor.decidableMemW finiteUniverse j w

/-- Hereditary naturality is decidable for the prototype. -/
def decidableIsHereditarilyNaturalUniverse (z : universeFunctor.toSlicePFunctor.W) :
    Decidable (universeFunctor.IsHereditarilyNatural z) :=
  FinitePresheafPFunctor.decidableIsHereditarilyNatural finiteUniverse z
