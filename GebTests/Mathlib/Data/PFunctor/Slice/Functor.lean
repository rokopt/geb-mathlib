/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Slice.Functor

/-!
# Tests for the slice polynomial functor wrapper
-/

set_option linter.privateModule false

open CategoryTheory SliceDomPFunctor SlicePFunctor

/-- A concrete slice polynomial functor for the wrapper tests (local, to
avoid a cross-test-file dependency). The shape-output map `q = id`
distinguishes the two shapes, so the wrapper tests exercise the output
index rather than collapsing. -/
def wrapperTestSlice : SlicePFunctor Bool Bool where
  A := Bool
  B := fun _ ↦ Bool
  r := fun x ↦ x.2
  q := id

/-- The categorical wrapper of `wrapperTestSlice`: a named value from
`Slice.Functor` (the module under test) that the examples below assert about. -/
def wrapperFunctor : CategoryTheory.Functor (Over Bool) (Over Bool) :=
  wrapperTestSlice.functor

-- The slice-valued functor forgets back to `domFunctor`.
example : wrapperFunctor ⋙ Over.forget Bool =
    wrapperTestSlice.toSliceDomPFunctor.domFunctor :=
  wrapperTestSlice.functor_comp_forget

-- The categorical object map is `Over.mk` of the choice-free `obj`.
example (Y : Over Bool) :
    wrapperFunctor.obj Y =
      Over.mk (↾ wrapperTestSlice.obj (ConcreteCategory.hom Y.hom)) :=
  wrapperTestSlice.functor_obj Y

-- The categorical morphism map's underlying function is the choice-free `map`
-- (the commuting hypothesis is irrelevant: any proof of it agrees).
example {Y Z : Over Bool} (g : Y ⟶ Z)
    (hg : ConcreteCategory.hom Z.hom ∘ ConcreteCategory.hom g.left =
      ConcreteCategory.hom Y.hom) :
    (wrapperFunctor.map g).left =
      ↾ wrapperTestSlice.map (ConcreteCategory.hom g.left) hg :=
  wrapperTestSlice.functor_map g
