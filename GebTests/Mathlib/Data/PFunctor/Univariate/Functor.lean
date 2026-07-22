/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Univariate.Functor
import GebTests.Mathlib.Data.PFunctor.Univariate.Fixtures

/-!
# Tests for the univariate `PFunctor` functor wrapper

A concrete polynomial functor exercises the categorical wrapper and its
agreement with the upstream `Obj` / `map`.

## Tags

polynomial functor, PFunctor, container
-/

set_option linter.privateModule false

open CategoryTheory

/-- The categorical wrapper of `testPFunctor`: a named value from the
module under test, so `lake shake` observes the import. -/
def testFunctor : CategoryTheory.Functor (Type 0) (Type 0) :=
  testPFunctor.functor.{0, 0, 0}

-- The object map is the upstream interpretation.
example (α : Type 0) : testFunctor.obj α = testPFunctor.Obj α :=
  testPFunctor.functor_obj α

-- The morphism map is the upstream action.
example {α β : Type 0} (f : α → β) :
    testFunctor.map (↾f) = ↾(testPFunctor.map f) :=
  testPFunctor.functor_map f
