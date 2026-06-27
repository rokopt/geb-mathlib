/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.Basic

-- Test files keep their declarations private; silence the
-- only-private-declarations lint.
set_option linter.privateModule false

/-!
# Tests for the presheaf-domain polynomial functor core
-/

open CategoryTheory PresheafDomPFunctorData

-- A caller can name the law condition to state things of that type.
example {I : Type} [Category I] (F : PresheafDomPFunctor I) : F.RestrComp :=
  F.isFunctorial.restr_comp
