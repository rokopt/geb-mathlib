/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Slice.Decidable

/-!
# Tests for the slice fiber and compatibility decidability instances

A concrete slice polynomial functor exercises `decidableDirectionOver`,
`decidableShapeOver`, `decidableForallDirection`, and
`decidableCompatible`: one `decide`-verdict pair per instance, on a
directly instantiated positive and negative case. The existing `wSlice`
fixture (`Slice.W`'s test module) is module-private and cannot be
imported, so this file declares its own.

## Tags

polynomial functor, slice category, decidability, FinEnum
-/

set_option linter.privateModule false

/-- A choice-free `FinEnum Bool` for the shape type. -/
instance finEnumBool : FinEnum Bool where
  card := 2
  equiv :=
    { toFun := fun b ↦ if b then 1 else 0
      invFun := fun i ↦ i == 1
      left_inv := Bool.rec rfl rfl
      right_inv := Fin.cases rfl (Fin.cases rfl (fun i ↦ i.elim0)) }
  decEq := inferInstance

/-- A slice endofunctor over `Bool`: shape `true` branches once, shape
`false` is a leaf. An `abbrev` so its projections unfold at instances
transparency; a plain `def` leaves `decide` stuck. -/
abbrev testSlice : SlicePFunctor.{0, 0, 0, 0} Bool Bool where
  A := Bool
  B := fun a ↦ cond a Unit Empty
  r := fun x ↦ x.1
  q := id

/-- The direction enumeration of `testSlice`, by cases on the shape.
`decEq` is ascribed explicitly, as a bare `inferInstance` asks for
`DecidableEq (testSlice.B a)`, which does not reduce. -/
instance finitaryTestSlice : testSlice.toPFunctor.Finitary
  | true => { card := 1
              equiv := { toFun := fun _ ↦ 0, invFun := fun _ ↦ (),
                         left_inv := fun _ ↦ rfl,
                         right_inv := fun i ↦ Fin.cases rfl (fun i ↦ i.elim0) i }
              decEq := (inferInstance : DecidableEq Unit) }
  | false => { card := 0
               equiv := { toFun := Empty.elim, invFun := Fin.elim0,
                          left_inv := fun x ↦ x.elim, right_inv := fun i ↦ i.elim0 }
               decEq := (inferInstance : DecidableEq Empty) }

/-- A direction lying over the index it is assigned. -/
def dirOverTrue : Bool := decide (testSlice.DirectionOver true true ())

/-- A direction not lying over the given index. -/
def dirOverFalse : Bool := decide (testSlice.DirectionOver true false ())

/-- A shape lying over its output index. -/
def shapeOverTrue : Bool := decide (testSlice.ShapeOver true true)

/-- A shape not lying over the given output index. -/
def shapeOverFalse : Bool := decide (testSlice.ShapeOver false true)

/-- A compatible direction assignment. -/
def compatTrue : Bool :=
  decide (testSlice.toSliceDomPFunctor.Compatible id true fun _ ↦ true)

/-- An incompatible direction assignment. -/
def compatFalse : Bool :=
  decide (testSlice.toSliceDomPFunctor.Compatible id true fun _ ↦ false)

example : dirOverTrue = true := by decide
example : dirOverFalse = false := by decide
example : shapeOverTrue = true := by decide
example : shapeOverFalse = false := by decide
example : compatTrue = true := by decide
example : compatFalse = false := by decide

/-- The admissible tree: the bare leaf, whose `OverInput` is vacuous. -/
def leafTree : testSlice.toPFunctor.W := WType.mk false Empty.elim

/-- An admissible tree is admitted. -/
def wValidTrue : Bool := decide (testSlice.WValid leafTree)

/-- An inadmissible tree: a `true`-node whose child has root index
`false`, violating `OverInput`. -/
def branchTree : testSlice.toPFunctor.W :=
  WType.mk true fun _ ↦ WType.mk false Empty.elim

/-- An inadmissible tree is rejected. -/
def wValidFalse : Bool := decide (testSlice.WValid branchTree)

example : wValidTrue = true := by decide
example : wValidFalse = false := by decide
