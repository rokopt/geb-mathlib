/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Univariate.W
import GebTests.Mathlib.Data.PFunctor.Univariate.Fixtures

/-!
# Tests for the W-type as the initial algebra

A concrete polynomial functor exercises the algebra, the uniqueness of
morphisms out of it, and the structure-map isomorphism.

## Tags

polynomial functor, W-type, initial algebra
-/

set_option linter.privateModule false

open CategoryTheory

/-- The W-type algebra of `testPFunctor`: a named value from the module
under test, so `lake shake` observes the import. It is an `abbrev`, not
a `def`: a semireducible `def` is not unfolded by instance synthesis, so
`Subsingleton (wTestAlgebra ⟶ B)` would fail to resolve against the
`Unique` introduced below. -/
abbrev wTestAlgebra : Endofunctor.Algebra (testPFunctor.functor.{0, 0, 0}) :=
  testPFunctor.wAlgebra

-- The structure-map isomorphism's forward map is the algebra's structure map.
example : (testPFunctor.wStrIso).hom = wTestAlgebra.str :=
  testPFunctor.wStrIso_hom

-- Any two algebra morphisms out of the W-type algebra agree.
example (B : Endofunctor.Algebra (testPFunctor.functor.{0, 0, 0}))
    (g h : wTestAlgebra ⟶ B) : g = h := by
  haveI := testPFunctor.wUniqueHom B
  exact Subsingleton.elim g h

/-- A concrete tree in `testPFunctor.W`: a branching root over two
leaves. -/
def testTree : testPFunctor.W :=
  WType.mk true (fun _ ↦ WType.mk false Empty.elim)

/-- A node-counting fold over `testPFunctor.W`. -/
def testNodeCount : testPFunctor.W → Nat :=
  WType.elim Nat fun x ↦ match x with
    | ⟨false, _⟩ => 1
    | ⟨true, f⟩ => 1 + f true + f false

-- The fold evaluates: the test tree has three nodes.
example : testNodeCount testTree = 3 := rfl
