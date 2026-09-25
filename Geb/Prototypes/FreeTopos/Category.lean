/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Model
public import Mathlib.CategoryTheory.Category.Basic

set_option doc.verso true in
/-!
# The category of a model of the theory of an elementary topos

A model of the theory is a category: its objects are the model's objects, and a morphism from
one object to another is an arrow with that domain and codomain; identities and composition are
the model's, and the laws of a category are the category block's axioms.

## Main definitions

* {lit}`ToposModel.Cat` — the objects of a model, carrying its category.

## Tags

elementary topos, model, category
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open CategoryTheory

universe v

namespace ToposModel

variable (T : ToposModel.{v})

/-- The objects of a model, carrying the model's category. -/
def Cat : Type v := T.Obj

instance : Category T.Cat where
  Hom a b := {f : T.Ar // T.domOf f = a ∧ T.codOf f = b}
  id a := ⟨T.idOf a, T.domOf_idOf a, T.codOf_idOf a⟩
  comp f g := ⟨T.compOf g.1 f.1 (f.2.2.trans g.2.1.symm),
    (T.domOf_compOf _).trans f.2.1, (T.codOf_compOf _).trans g.2.2⟩
  id_comp f := by
    obtain ⟨f, rfl, rfl⟩ := f
    exact Subtype.ext (T.compOf_idOf f)
  comp_id f := by
    obtain ⟨f, rfl, rfl⟩ := f
    exact Subtype.ext (T.idOf_compOf f)
  assoc f g h := by
    obtain ⟨f, rfl, rfl⟩ := f
    obtain ⟨g, hg, rfl⟩ := g
    obtain ⟨h, hh, rfl⟩ := h
    exact Subtype.ext (T.compOf_assoc hg.symm hh.symm)

end ToposModel

end Geb.FreeTopos

end
