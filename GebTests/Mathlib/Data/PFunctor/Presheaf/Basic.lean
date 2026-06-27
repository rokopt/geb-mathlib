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

-- `obj` is the `IsNatural` subtype of the slice object on `pZ Z`.
example {I : Type} [Category I] (F : PresheafDomPFunctor I) (Z : Iᵒᵖ ⥤ Type) :
    F.obj Z = { x : F.toSliceDomPFunctor.obj (PresheafDomPFunctorData.pZ Z)
      // F.IsNatural x } := rfl

-- `map` of the hand-built identity transformation is the identity, by
-- `map_id`. The identity transformation is hand-built (not `NatTrans.id`)
-- to stay choice-free.
example {I : Type} [Category I] (F : PresheafDomPFunctor I) (Z : Iᵒᵖ ⥤ Type) :
    F.map { app := fun i => 𝟙 (Z.obj i), naturality := fun _ _ _ => rfl } =
      (id : F.obj Z → F.obj Z) := F.map_id Z

-- The full bundle projects the inherited dom law and names a `J`-side law.
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J) :
    F.RestrComp := F.isFunctorial.restr_comp
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J) :
    F.TagRestrComp := F.isFunctorial.tagRestr_comp

-- The output presheaf's fibre over `j` is the `t`-tagged subtype of the dom
-- functor's value on `Z`.
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J)
    (Z : Iᵒᵖ ⥤ Type) (j : J) :
    (F.objPresheaf Z).obj ⟨j⟩ =
      { z : F.toPresheafDomPFunctorData.obj Z // F.t z.1.1.1 = j } := rfl
