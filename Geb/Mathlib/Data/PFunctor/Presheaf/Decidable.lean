/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.W
public import Geb.Mathlib.Data.PFunctor.Slice.Decidable
public import Geb.Mathlib.Data.W.Basic

/-!
# Decidability of a direction assignment's naturality

`PresheafDomPFunctorData.IsNatural` is a quantifier over the objects, the
hom-sets, and the directions of the index category, of an equality in a fiber
of the input presheaf. It is decidable when the functor is finitary, the index
category has finitely many objects and finite hom-sets, and the input
presheaf's values have decidable equality.

## Main definitions

* `PresheafDomPFunctorData.decidableIsNatural` — decidability of `IsNatural`.

## Tags

polynomial functor, presheaf, naturality, decidability, FinEnum
-/

public section

open CategoryTheory

universe uI uA uB vI uZ

namespace PresheafDomPFunctorData

/-- Naturality of a direction assignment is decidable when the functor is
finitary, the index category has finitely many objects and finite
hom-sets, and the input presheaf's values have decidable equality. Its
subject is a slice object over `elemProj Z`, not a `PresheafDomPFunctorData.obj Z`:
the latter is the `IsNatural` subtype itself, on which the predicate
holds by projection. -/
instance decidableIsNatural {I : Type uI} [Category.{vI} I]
    (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I) {Z : Iᵒᵖ ⥤ Type uZ}
    [F.Finitary] [FinEnum I] [∀ i i' : I, FinEnum (i' ⟶ i)]
    [∀ i : I, DecidableEq (Z.obj ⟨i⟩)]
    (x : F.toSliceDomPFunctor.Obj (elemProj Z)) : Decidable (F.IsNatural x) :=
  inferInstanceAs (Decidable (∀ ⦃i i' : I⦄ (f : i' ⟶ i)
    (b : F.toSliceDomPFunctor.Direction x.1.1 i),
      F.value x (F.directionRestr x.1.1 f b) = Z.map f.op (F.value x b)))

end PresheafDomPFunctorData
