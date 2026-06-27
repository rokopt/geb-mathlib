/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module -- shake: keep-all

import Geb.Mathlib.Data.PFunctor.Presheaf.Functor

set_option linter.privateModule false

/-!
# Tests for the presheaf-domain polynomial functor wrapper
-/

open CategoryTheory PresheafDomPFunctorData PresheafPFunctor

-- The categorical object map is the choice-free `obj`.
example {I : Type} [Category I] (F : PresheafDomPFunctorData I) (Z : Iᵒᵖ ⥤ Type) :
    F.domFunctor.obj Z = F.obj Z :=
  rfl

-- The categorical morphism map is `↾` of the choice-free `map` of the bare
-- natural transformation underlying the functor-category hom.
example {I : Type} [Category I] (F : PresheafDomPFunctorData I) {Z Z' : Iᵒᵖ ⥤ Type}
    (h : Z ⟶ Z') :
    F.domFunctor.map h = ↾ F.map h :=
  rfl

-- The presheaf-valued functor's object map is the choice-free `objPresheaf`.
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J)
    (Z : Iᵒᵖ ⥤ Type) : F.functor.obj Z = F.objPresheaf Z :=
  F.functor_obj Z

