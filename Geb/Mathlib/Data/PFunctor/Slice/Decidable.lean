/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Geb.Mathlib.Data.PFunctor.Univariate.Finitary
public import Geb.Mathlib.Data.FinEnum
import Geb.Mathlib.Data.W.Basic

/-!
# Decidability of the slice functor's fiber and compatibility predicates

`SliceDomPFunctor.DirectionOver` / `SlicePFunctor.ShapeOver` are equalities
against a base or output index, decidable given decidable equality on that
index. A quantifier over the directions of a shape lying over an index is
decidable given `PFunctor.Finitary`, via `FinEnum.decidableForallSubtype`.
`SliceDomPFunctor.Compatible` is, by definition, an equality of functions out
of the (finitary) direction type, decidable via `FinEnum.decidablePiFinEnum`.

## Main definitions

* `SliceDomPFunctor.decidableDirectionOver` — decidability of
  `DirectionOver`.
* `SlicePFunctor.decidableShapeOver` — decidability of `ShapeOver`.
* `SliceDomPFunctor.decidableForallDirection` — decidability of a
  quantifier over the directions of a shape lying over an index.
* `SliceDomPFunctor.decidableCompatible` — decidability of `Compatible`.

## Tags

polynomial functor, slice category, decidability, FinEnum
-/

public section

universe uA uB uD uC uI uX

namespace SliceDomPFunctor

/-- Whether a direction lies over a given base index is decidable when
the base has decidable equality. No finiteness is needed. -/
instance decidableDirectionOver {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    [DecidableEq dom] (a : F.A) (i : dom) : DecidablePred (F.DirectionOver a i) :=
  fun b ↦ decidable_of_iff (F.rCurried a b = i) Iff.rfl

/-- A quantifier over the directions of shape `a` lying over `i` is
decidable. Stated at `Direction` rather than left to
`FinEnum.decidableForallSubtype`: `Direction` is a `def`, and instance
resolution does not unfold it to a `Subtype`. -/
instance decidableForallDirection {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    [F.Finitary] [DecidableEq dom] (a : F.A) (i : dom)
    {q : F.Direction a i → Prop} [DecidablePred q] : Decidable (∀ b, q b) :=
  inferInstanceAs (Decidable (∀ b : Subtype (F.DirectionOver a i), q b))

/-- Compatibility of a direction assignment with a projection is
decidable: `Compatible p a v` is by definition the function equality
`p ∘ v = F.r ∘ Sigma.mk a` out of the finite direction type, decided by
`FinEnum.decidablePiFinEnum`. -/
instance decidableCompatible {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    [F.Finitary] [DecidableEq dom] {X : Type uX} (p : X → dom)
    (a : F.A) (v : F.B a → X) : Decidable (F.Compatible p a v) :=
  decidable_of_iff (p ∘ v = F.r ∘ Sigma.mk a) Iff.rfl

end SliceDomPFunctor

namespace SlicePFunctor

/-- Whether a shape lies over a given output index is decidable when the
codomain has decidable equality. -/
instance decidableShapeOver {dom : Type uD} {cod : Type uC}
    (F : SlicePFunctor.{uA, uB, uD, uC} dom cod) [DecidableEq cod] (j : cod) :
    DecidablePred (F.ShapeOver j) :=
  fun a ↦ decidable_of_iff (F.q a = j) Iff.rfl

end SlicePFunctor
