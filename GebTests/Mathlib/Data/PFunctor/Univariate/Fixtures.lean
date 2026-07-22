/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Shared fixture for the univariate `PFunctor` tests

The concrete polynomial functor the `Univariate` test modules share.
It is defined once here rather than repeated per module so the three
test modules exercise the same object.

## Main definitions

* `testPFunctor` — two shapes: a leaf and a binary branch.

## Tags

polynomial functor, PFunctor, container
-/

-- `testPFunctor` must be `@[expose]`d so its shape and direction types
-- unfold across the module boundary (a compiler limitation for
-- `module`s), and `expose` is meaningful on public definitions only.
@[expose] public section

/-- A concrete polynomial functor: two shapes, `false` a leaf (no
directions) and `true` branching in two (directions `Bool`). -/
def testPFunctor : PFunctor.{0, 0} := ⟨Bool, fun b ↦ cond b Bool Empty⟩
