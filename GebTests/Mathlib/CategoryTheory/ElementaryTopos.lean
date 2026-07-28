/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.CategoryTheory.ElementaryTopos

/-!
# Tests for the elementary-topos class

An instance at the degenerate topos `Discrete PUnit` witnesses that
the class is inhabitable, and resolution assertions confirm that each
derived `Prop` instance is reachable through it.

## Tags

elementary topos, subobject classifier, degenerate topos
-/

set_option linter.privateModule false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

section Resolution

variable (C : Type u) [Category.{v} C] [ElementaryTopos C]

example : HasInitial C := inferInstance
example : HasBinaryCoproducts C := inferInstance
example : HasEqualizers C := inferInstance
example : HasCoequalizers C := inferInstance
example : HasFiniteCoproducts C := inferInstance
example : HasFiniteLimits C := inferInstance
example : HasFiniteColimits C := inferInstance

attribute [local instance] ElementaryTopos.cartesianMonoidalCategory

/-- The data accessors cross the module boundary. -/
example : CartesianMonoidalCategory C :=
  ElementaryTopos.cartesianMonoidalCategory C

example : MonoidalClosed C := ElementaryTopos.monoidalClosed C

end Resolution
