/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Univariate.Initial
import GebTests.Mathlib.Data.PFunctor.Univariate.Fixtures

/-!
# Tests for the W-type algebra's initiality

Exercises the `Limits.IsInitial` packaging of the W-type algebra.

## Tags

polynomial functor, W-type, initial algebra
-/

set_option linter.privateModule false

open CategoryTheory

/-- The initiality witness: a named value from the module under test, so
`lake shake` observes the import. -/
def initialTestWitness :
    Limits.IsInitial (testPFunctor.wAlgebra) :=
  testPFunctor.wIsInitial

-- The witness yields a morphism into any algebra.
example (B : Endofunctor.Algebra (testPFunctor.functor.{0, 0, 0})) :
    testPFunctor.wAlgebra ⟶ B :=
  initialTestWitness.to B

-- The witness's morphism is the underlying fold, not merely some morphism.
example (B : Endofunctor.Algebra (testPFunctor.functor.{0, 0, 0})) :
    initialTestWitness.to B = testPFunctor.wElim B :=
  testPFunctor.wIsInitial_to B
