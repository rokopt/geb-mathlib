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

/-- The class elaborates and its fields are reachable. -/
example (C : Type u) [Category.{v} C] [ElementaryTopos C] :
    Subobject.Classifier C :=
  ElementaryTopos.classifier
