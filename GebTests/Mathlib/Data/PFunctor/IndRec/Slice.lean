/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Slice

/-!
# Tests for slice polynomial functor conversions

`IR.sliceCode` translates a `SlicePFunctor` to an `IR` code (Lemma 1);
`IR.toSlicePFunctor` translates in the other direction (Lemma 2 /
Definition 5). `rfl` tests check structural correctness at each
translation.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

inductive-recursive, polynomial functor, slice category, container
-/

@[expose] public section

open CategoryTheory IndRec

/-- A test slice polynomial functor: shape `Bool`, directions `Nat`,
all directions map to `PUnit.unit`, all shapes map to `PUnit.unit`. -/
def testSlice : SlicePFunctor.{0, 0, 0, 0} PUnit PUnit :=
  { toPFunctor := ⟨Bool, fun _ ↦ Nat⟩
  , r := fun _ ↦ PUnit.unit
  , q := fun _ ↦ PUnit.unit }

/-- The `IR` code for `testSlice`. -/
def testSliceCode : IR.{0, 0, 0, 0} PUnit PUnit :=
  IR.sliceCode PUnit PUnit testSlice

/-- `sliceCode` produces the expected structure: `sigma` over shapes,
`delta` over directions, `sigma` over the compatibility constraint,
`iota` at the output index. -/
example :
    testSliceCode =
      IR.sigma PUnit PUnit Bool fun a ↦
        IR.delta PUnit PUnit Nat fun assign ↦
          IR.sigma PUnit PUnit
            (ULift.{0} (PLift (∀ b, assign b = testSlice.rCurried a b))) fun _ ↦
            IR.iota PUnit PUnit PUnit.unit :=
  rfl
