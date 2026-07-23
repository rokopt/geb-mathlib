/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.FinEnum

/-!
# Tests for the choice-free `FinEnum` decidability instances

Each instance is exercised by a closed `decide`, in both directions, so
that a failure to reduce is caught. Verdicts are named `def`s rather than
bare `example`s: an `example` adds no constant to the environment, so the
axiom linter cannot see it.

## Tags

FinEnum, decidability, test
-/

set_option linter.privateModule false

/-- A choice-free `FinEnum Bool`, built from the structure fields. The
`Equiv` laws are proved by case analysis: `decide` would route through
`Bool`'s `Fintype` instance and reintroduce `Classical.choice`. -/
instance finEnumBool : FinEnum Bool where
  card := 2
  equiv :=
    { toFun := fun b ↦ if b then 1 else 0
      invFun := fun i ↦ i == 1
      left_inv := Bool.rec rfl rfl
      right_inv := Fin.cases rfl (Fin.cases rfl (fun i ↦ i.elim0)) }
  decEq := inferInstance

/-- A bounded `∀` that holds. -/
def forallTrue : Bool := decide (∀ b : Bool, b || !b)

/-- A bounded `∀` that fails. -/
def forallFalse : Bool := decide (∀ b : Bool, b)

/-- A `∀` over a decidable subtype that holds. -/
def subtypeTrue : Bool := decide (∀ x : { b : Bool // b = true }, x.1 = true)

/-- A `∀` over a decidable subtype that fails. -/
def subtypeFalse : Bool := decide (∀ x : { b : Bool // b = true }, x.1 = false)

/-- A function equality that holds. -/
def funTrue : Bool := decide ((fun b : Bool ↦ !b) = fun b : Bool ↦ !b)

/-- A function equality that fails. -/
def funFalse : Bool := decide ((fun b : Bool ↦ !b) = fun b : Bool ↦ b)

example : forallTrue = true := by decide
example : forallFalse = false := by decide
example : subtypeTrue = true := by decide
example : subtypeFalse = false := by decide
example : funTrue = true := by decide
example : funFalse = false := by decide
