/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.W

/-!
# Tests for the data type and decoder described by an IR code

`rfl` tests that `IR.W.mk` reduces on a closed code and that
`IR.wDecode` reads back the decoding the interpretation assigns the
node.

## Tags

inductive-recursive, initial algebra, W-type
-/

@[expose] public section

open CategoryTheory IndRec

/-- A closed endo-code over the natural numbers: a single non-recursive
field, a natural number, which the node decodes to. -/
def testLitCode : IR.{0, 0, 0, 0} Nat Nat :=
  IR.sigma Nat Nat Nat fun n ↦ IR.iota Nat Nat n

/-- The element of the described data type carrying the literal `n`. -/
def testLit (n : Nat) : IR.W.{0, 0, 0} Nat testLitCode :=
  IR.W.mk Nat testLitCode ⟨n, ULift.up ()⟩

-- The decoder reads back the literal, by reduction alone.
example : IR.wDecode Nat testLitCode (testLit 5) = 5 :=
  rfl

/-- A closed endo-code with a recursive field: one recursive field whose
decoding the node returns incremented. -/
def testSuccCode : IR.{0, 0, 0, 0} Nat Nat :=
  IR.delta Nat Nat PUnit fun n ↦ IR.iota Nat Nat (n PUnit.unit + 1)

/-- The element built from a recursive field, at the code with a
recursive field. -/
def testSucc (x : IR.W.{0, 0, 0} Nat testSuccCode) : IR.W.{0, 0, 0} Nat testSuccCode :=
  IR.W.mk Nat testSuccCode ⟨fun _ ↦ x, ULift.up ()⟩

-- The recursive field's decoding is what the node's decoding is
-- computed from.
example (x : IR.W.{0, 0, 0} Nat testSuccCode) :
    IR.wDecode Nat testSuccCode (testSucc x) =
      IR.wDecode Nat testSuccCode x + 1 :=
  rfl
