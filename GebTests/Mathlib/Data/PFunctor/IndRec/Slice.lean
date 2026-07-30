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

/-- A simple `IR` code: `iota PUnit.unit`. -/
def testIRiota : IR.{0, 0, 0, 0} PUnit PUnit :=
  IR.iota PUnit PUnit PUnit.unit

/-- The iota case `toSlicePFunctorIota` reduces to the constant
slice polynomial: one shape, no directions, output index `o`. -/
example (o : PUnit) :
    IR.toSlicePFunctorIota PUnit PUnit o =
      { toPFunctor := ⟨PUnit, fun _ ↦ PEmpty⟩
      , r := fun ⟨_, b⟩ ↦ PEmpty.elim b
      , q := fun _ ↦ o } :=
  rfl

/-- `toSlicePFunctor` at `iota` satisfies the computation rule
(definitional). -/
example :
    IR.toSlicePFunctor PUnit PUnit testIRiota =
      IR.toSlicePFunctorIota PUnit PUnit PUnit.unit :=
  rfl

/-- The sigma case `toSlicePFunctorSigma`, expressed through
`SlicePFunctor.coprod`, reduces to the componentwise coproduct of
Definition 5, clause 2. The index types are `Bool` rather than `PUnit`
so that the `r` and `q` components are discriminating. -/
example (A : Type) (sub : A → SlicePFunctor.{0, 0, 0, 0} Bool Bool) :
    IR.toSlicePFunctorSigma Bool Bool A sub =
      { toPFunctor := ⟨Σ a, (sub a).toPFunctor.A,
          fun ⟨a, sa⟩ ↦ (sub a).toPFunctor.B sa⟩
      , r := fun ⟨⟨a, sa⟩, p⟩ ↦ (sub a).r ⟨sa, p⟩
      , q := fun ⟨a, sa⟩ ↦ (sub a).q sa } :=
  rfl

/-- The delta case `toSlicePFunctorDelta`, expressed through
`SlicePFunctor.coprod`, reduces to the shape-indexed coproduct of
Definition 5, clause 3. Shapes, directions and the shape-output map are
checked as whole components; the direction-input map is checked on each
branch of the cotuple, since the two cotuple presentations agree on every
constructor but are not compared definitionally at a variable
discriminant. -/
example (B : Type) (sub : (B → Bool) → SlicePFunctor.{0, 0, 0, 0} Bool Bool) :
    (IR.toSlicePFunctorDelta Bool Bool B sub).toPFunctor =
      ⟨Σ (i : B → Bool), (sub i).toPFunctor.A,
        fun ⟨i, sa⟩ ↦ Sum B ((sub i).toPFunctor.B sa)⟩ :=
  rfl

example (B : Type) (sub : (B → Bool) → SlicePFunctor.{0, 0, 0, 0} Bool Bool) :
    (IR.toSlicePFunctorDelta Bool Bool B sub).q = fun ⟨i, sa⟩ ↦ (sub i).q sa :=
  rfl

/-- The cotuple's arity branch: a direction of the adjoined arity `B` is
sent to its image under the assignment `i`. -/
example (B : Type) (sub : (B → Bool) → SlicePFunctor.{0, 0, 0, 0} Bool Bool)
    (i : B → Bool) (sa : (sub i).toPFunctor.A) (b : B) :
    (IR.toSlicePFunctorDelta Bool Bool B sub).r ⟨⟨i, sa⟩, Sum.inl b⟩ = i b :=
  rfl

/-- The cotuple's sub-polynomial branch: a direction of `sub i` keeps the
direction-input map it had there. -/
example (B : Type) (sub : (B → Bool) → SlicePFunctor.{0, 0, 0, 0} Bool Bool)
    (i : B → Bool) (sa : (sub i).toPFunctor.A) (p' : (sub i).toPFunctor.B sa) :
    (IR.toSlicePFunctorDelta Bool Bool B sub).r ⟨⟨i, sa⟩, Sum.inr p'⟩ =
      (sub i).r ⟨sa, p'⟩ :=
  rfl
