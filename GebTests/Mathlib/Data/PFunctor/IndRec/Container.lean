/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Container

/-!
# Tests for container codes

A container is translated to an `IR` code over the unit type by
`contCode`, following Example 1 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]; `rfl` tests check that
an interpreted name decodes to the unit element, including at
separated arity universes.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

inductive-recursive, container
-/

@[expose] public section

open CategoryTheory IndRec

-- A simple container (a `PFunctor`) is translated to an `IR` code
-- over the unit type by `contCode`.

/-- A test container: shape `Bool`, with `Nat` directions under each
shape. -/
def testCont : PFunctor.{0, 0} := ⟨Bool, fun _ ↦ Nat⟩

/-- The `IR` code over the unit type representing `testCont`. -/
def testContCode : IR.{0, 0, 0, 0} PUnit PUnit := contCode testCont

/-- An input family over the unit type: a single name. -/
def testContX : FreeCoprodCompDisc.{0, 0} PUnit :=
  ⟨PUnit, fun _ ↦ PUnit.unit⟩

-- A name in the interpreted container pairs a shape, a direction
-- assignment into the input family, and the single name of the
-- constant `iota` interpretation; it decodes to the unit element
-- (Example 1's `(s : S) × (P s → X) × 1`).
example (s : Bool) (g : Nat → PUnit) :
    (IR.interpObj PUnit PUnit testContCode testContX).2
        ⟨s, g, ULift.up ()⟩ = PUnit.unit :=
  rfl

/-- A test container with separated field universes: shape `ULift Bool`
at universe `1`, with `Nat` directions at universe `0` under each
shape. -/
def testContSep : PFunctor.{1, 0} := ⟨ULift Bool, fun _ ↦ Nat⟩

/-- The `IR` code over the unit type representing `testContSep`: the
arity universes are instantiated off the diagonal (`uA ≠ uB`). -/
def testContSepCode : IR.{1, 0, 0, 0} PUnit PUnit := contCode testContSep

/-- An input family over the unit type at the matching index universe:
a single name. -/
def testContSepX : FreeCoprodCompDisc.{1, 0} PUnit :=
  ⟨PUnit, fun _ ↦ PUnit.unit⟩

-- The interpreted-name decoding is preserved at separated arity
-- universes.
example (s : ULift Bool) (g : Nat → PUnit) :
    (IR.interpObj PUnit PUnit testContSepCode testContSepX).2
        ⟨s, g, ULift.up ()⟩ = PUnit.unit :=
  rfl
