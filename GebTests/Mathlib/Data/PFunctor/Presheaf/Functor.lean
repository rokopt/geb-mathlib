/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.Functor

/-!
# Tests for the presheaf-domain polynomial functor wrapper
-/

set_option linter.privateModule false

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
-- Named (rather than an `example`) so `lake shake` sees `Presheaf.Functor` is
-- used: the module's declarations are otherwise exercised only in `example`s,
-- which leave no constant in the `.olean`.
theorem functor_obj_eq {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J)
    (Z : Iᵒᵖ ⥤ Type) : F.functor.obj Z = F.objPresheaf Z :=
  F.functor_obj Z

-- The presheaf-valued functor's morphism map is the dom `map`, restricted to the
-- `q`-indexed fibre.
theorem functor_map_app {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J)
    {Z Z' : Iᵒᵖ ⥤ Type} (α : Z ⟶ Z') (X : Jᵒᵖ) (w : (F.functor.obj Z).obj X) :
    (F.functor.map α).app X w =
      (⟨F.toPresheafDomPFunctorData.map α w.1, w.2⟩ : (F.functor.obj Z').obj X) :=
  F.functor_map α X w
