/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.FinCategory
public import GebTests.Mathlib.CategoryTheory.FinCat.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Tests for the diagonal `FinCategory`

Two assertions: `FinCategory` resolves at coinciding object and morphism
levels for the generated category of `terminalCat`, and the object-type
cardinality of the generated category of `walkingArrow` is `2`. It is
allowlisted, a test of a `Classical`-allowed wrapper being itself
`Classical`-dependent.

## Tags

finite category, fintype, choice, small category
-/

@[expose] public section

open CategoryTheory

/-- Assertion 1: `FinCategory` resolves at coinciding object and morphism
levels, picking up `FinCat.Obj.category.{0, 0}` as the underlying
`SmallCategory` instance. -/
example : FinCategory (FinCat.Obj.{0} terminalCat) := inferInstance

/-- Assertion 2: the object-type cardinality of the generated category of
`walkingArrow` is its object count, `2`, sourced through the `fintypeObj`
field of `FinCat.Obj.finCategory` via `FinCategory.fintypeObj`'s instance
attribute. -/
example : Fintype.card (FinCat.Obj.{0} walkingArrow) = 2 := by decide
