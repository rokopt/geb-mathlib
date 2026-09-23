/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Guarded -- shake: keep
public import Geb.Prototypes.MType.Equiv -- shake: keep
public import GebTests.Prototypes.Definition.Basic -- shake: keep

public meta import Geb.Prototypes.Definition.Guarded -- shake: keep
public meta import Geb.Prototypes.MType.Equiv -- shake: keep
public meta import GebTests.Prototypes.Definition.Basic -- shake: keep

set_option doc.verso true in
/-!
# Examples of guarded blocks

Bitstreams defined by guarded blocks. The block {lit}`zeroOne` states {lit}`x = 0 :: 1 :: x`,
whose body has depth two and refers back to its own export; the block {lit}`oneThen` states
{lit}`x = 1 :: y` for an imported stream {lit}`y`. Each solution's prefix is read through the
equivalence of the M-type constructed from W-types with mathlib's.

## Main definitions

* {lit}`zeroOne` is the block {lit}`x = 0 :: 1 :: x`.
* {lit}`oneThen` is the block {lit}`x = 1 :: y`, with {lit}`y` imported.
* {lit}`prefixOf` reads the first bits of a stream.

## Main statements

* {lit}`zeroOne_unique` states that every solution of {lit}`zeroOne` is the corecursive one.

## Tags

guarded recursion, bitstream, M-type, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.GuardedTests

open PFunctor Geb.Definition.Tests

/-- The block {lit}`x = 0 :: 1 :: x`. -/
def zeroOne : GuardedBlock BitStream.sig Empty Unit := fun _ ↦
  .inl ⟨some false, fun _ ↦ .liftBind (some true) fun _ ↦ .pure (.inr ())⟩

/-- The block {lit}`x = 1 :: y`, with {lit}`y` imported. -/
def oneThen : GuardedBlock BitStream.sig Unit Unit := fun _ ↦
  .inl ⟨some true, fun _ ↦ .pure (.inl ())⟩

/-- The alternating stream from {lit}`false`, as an element of the M-type built from W-types. -/
def alternatingM : MType.M BitStream.sig := MType.M.corec alternating false

/-- The first {lit}`n` bits of a stream. -/
def prefixOf (n : ℕ) (x : MType.M BitStream.sig) : List Bool :=
  (BitStream.seqEquiv (MType.mEquiv BitStream.sig x)).take n

/-- Every solution of {name}`zeroOne` is the corecursive one. -/
theorem zeroOne_unique (v : Unit → MType.M BitStream.sig)
    (h : IsSolution MType.M.mk Empty.elim zeroOne.toBlock v) :
    v = GuardedBlock.solution Empty.elim zeroOne :=
  GuardedBlock.eq_of_isSolution _ _ h (GuardedBlock.isSolution_solution _ _)

#guard prefixOf 6 (GuardedBlock.solution Empty.elim zeroOne ()) =
  [false, true, false, true, false, true]
#guard prefixOf 5 (GuardedBlock.solution (fun _ ↦ alternatingM) oneThen ()) =
  [true, false, true, false, true]

end Geb.Definition.GuardedTests

end
