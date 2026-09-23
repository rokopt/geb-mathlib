/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Univariate.Obj
import GebTests.Mathlib.Data.PFunctor.Univariate.Fixtures

/-!
# Tests for the nodes of a polynomial functor

The concrete polynomial functor of the fixture exercises injectivity of
`PFunctor.map` and the child of a node read along a shape equation.

## Tags

polynomial functor, PFunctor, node
-/

set_option linter.privateModule false

/-- Mapping the successor function over the fixture's nodes is injective. -/
theorem testMapSucc_injective : Function.Injective (testPFunctor.map Nat.succ) :=
  PFunctor.map_injective Nat.succ_injective

-- Read along the reflexive equation, `sndOfEq` is the node's child.
example (f : testPFunctor.B true → ℕ) (b : testPFunctor.B true) :
    (PFunctor.Obj.mk true f : testPFunctor ℕ).sndOfEq rfl b = f b :=
  rfl

-- A node is its shape over its `sndOfEq` children.
example (x : testPFunctor ℕ) : PFunctor.Obj.mk x.fst (x.sndOfEq rfl) = x :=
  PFunctor.Obj.mk_sndOfEq x rfl
