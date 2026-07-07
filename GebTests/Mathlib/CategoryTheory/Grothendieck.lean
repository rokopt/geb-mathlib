/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import Geb.Mathlib.CategoryTheory.Grothendieck

set_option linter.privateModule false

/-!
# Tests for the covariant and contravariant Grothendieck constructions
-/

open CategoryTheory

/-! ## Covariant `functorToCat` -/

/-- A concrete covariant `Cat`-valued functor: constant at `Type`. -/
def constTypeCovariant : Type ⥤ Cat.{0, 1} :=
  (Functor.const (Type : Type 1)).obj (Cat.of Type)

/-- `functorToCat` applied to a constant functor yields the
Grothendieck construction on the nose. -/
theorem functorToCat_obj_constTypeCovariant :
    (Grothendieck.functorToCat (E := Cat.of (Type : Type 1))).obj
        constTypeCovariant =
      Cat.of (Grothendieck constTypeCovariant) :=
  rfl
