/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.Finite.W
import GebTests.Mathlib.Data.PFunctor.Presheaf.Fixtures

/-!
# Tests for the endofunctor-tier finite presheaf W-type decidability

Reduction tests for the endofunctor-tier declarations on
`FinitePresheafPFunctor`. The shared `finiteWFixture` supplies the bundled
finiteness evidence, and `decide` verifies that `wValidBool`, `memWBool`,
`decidableEqW`, and `decidableMemW` reduce correctly. The three ways a tree can
fail to lie in the carrier presheaf's fiber — inadmissibility, wrong index, and
failure of hereditary naturality — are exercised separately, so each conjunct of
`memWBool` is discriminated.

## Tags

polynomial functor, presheaf, finite, W-type, decidability, reduction test
-/

set_option linter.privateModule false

open CategoryTheory PresheafFixture

universe uI uA uB vI

/-! ## Resolution tests -/

/-- `decidableIsHereditarilyNatural` is reachable by inference for a goal stated
at `SlicePFunctor.W`, the type `IsHereditarilyNatural` itself takes. -/
example {I : Type uI} [Category.{vI} I]
    (F : FinitePresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (z : F.toPresheafPFunctor.toSlicePFunctor.W) :
    Decidable (F.toPresheafPFunctor.IsHereditarilyNatural z) := inferInstance

/-- `decidableMemW` is reachable by inference. -/
example {I : Type uI} [Category.{vI} I]
    (F : FinitePresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) (j : I)
    (w : F.toPresheafPFunctor.toPFunctor.W) :
    Decidable (F.toPresheafPFunctor.MemW j w) := inferInstance

/-! ## Combined validator tests

`wValidBool` conjoins slice admissibility and hereditary naturality. Since it is
`@[expose]` and `finiteWFixture` is `@[reducible]`, plain function application
reduces. -/

/-- The good tree passes the combined validator. -/
def wValidGood : Bool := finiteWFixture.wValidBool goodTree.1

/-- The bad tree (fails naturality) fails the combined validator. -/
def wValidBad : Bool := finiteWFixture.wValidBool badTree.1

/-- An inadmissible tree fails the combined validator. -/
def wValidInadmissible : Bool := finiteWFixture.wValidBool inadmissibleTree

example : wValidGood = true := by decide
example : wValidBad = false := by decide
example : wValidInadmissible = false := by decide

/-! ## DecidableEq tests -/

/-- DecidableEq: two equal leaf trees. -/
def eqTrue : Bool :=
  @decide _ (finiteWFixture.decidableEqW (leafTree .L0a).1 (leafTree .L0a).1)

/-- DecidableEq: two distinct leaf trees. -/
def eqFalse : Bool :=
  @decide _ (finiteWFixture.decidableEqW (leafTree .L0a).1 (leafTree .L0b).1)

example : eqTrue = true := by decide
example : eqFalse = false := by decide

/-! ## Fiber-membership tests

Each conjunct of `memWBool` is discriminated separately: `memWWrongIndex` fails
only the index test, `memWUnnatural` only hereditary naturality, and
`memWInadmissible` only admissibility. -/

/-- Fiber membership: `goodTree` lies in the fiber over index `1`. -/
def memWTrue : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableMemW finiteWFixture 1 goodTree.1)

/-- Fiber membership fails on the index: `goodTree` is indexed at `1`, not `0`. -/
def memWWrongIndex : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableMemW finiteWFixture 0 goodTree.1)

/-- Fiber membership fails on hereditary naturality: `badTree` is admissible and
indexed at `1`, but unnatural at the root. -/
def memWUnnatural : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableMemW finiteWFixture 1 badTree.1)

/-- Fiber membership fails on admissibility: `inadmissibleTree` is not a valid
slice W-tree at all. -/
def memWInadmissible : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableMemW finiteWFixture 1 inadmissibleTree)

example : memWTrue = true := by decide
example : memWWrongIndex = false := by decide
example : memWUnnatural = false := by decide
example : memWInadmissible = false := by decide
