/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.PFunctor.Univariate.Basic
public import Geb.Mathlib.Data.PFunctor.Slice.Basic

/-!

## Main statements

## References

## Tags
-/

@[expose] public section

namespace GebProto

namespace PFElemCat

universe uA uB v

variable (F : PFunctor.{uA, uB})

/-- Objects of the category of elements of a `PFunctor`. -/
def Obj : Type (max uA uB (v + 1)) := Σ x : Type v, F.Obj x

/-- Morphisms of the category of elements of a `PFunctor`. -/
def Hom (e e' : Obj.{uA, uB, v} F) : Type v :=
  { f : (e.1 → e'.1) // F.map f e.2 = e'.2 }

end PFElemCat

namespace PFSliceCat

universe uA uB v w

variable (F : PFunctor.{uA, uB})

set_option linter.checkUnivs false in
/-- A slice over a `PFunctor` within the category of polynomial
functors is determined by a coproduct of objects of the category
of elements of the `PFunctor`. -/
def Obj : Type (max uA uB (v + 1) (w + 1)) :=
  Σ i : Type w, i → PFElemCat.Obj.{uA, uB, v} F

end PFSliceCat

namespace LargeIR

universe uA uB v w x

/- A functor between Grothendieck constructions determines,
and is determined by, a set of data beginning with a functor
between base categories. To build a PRA functor specifically
between Grothendieck constructions, we obtain, and require, a
PRA functor between the base categories. Here we call it `B`,
the base functor, which we may view as an endofunctor on
`Type (max uA uB v)` (for any universe `v`), and thus is one
component of a functor between Grothendieck constructions with
domain `Type (max uA uB v)` (or its opposite category, for a
contravariant Grothendieck construction). -/
variable (B : PFunctor.{uA, uB})

/-- To form an endofunctor on `Fam` in particular -- the Grothendieck
construction from `Type^op` which produces the slice category, with the
morphisms going to base change -- we use `B` to take the input shape
type to an output shape type, and thus require a functor to take a slice
over the input shape type to a slice over the output shape type.  So
we need a functor which, for a given type `X`, produces a slice polynomial
functor from `Type/X` to `Type/B(X)`. -/
def ET : Type (max (uA + 1) (uB + 1) (v + 1)) :=
  Π X : Type (max uA uB v),
    SlicePFunctor.{uA, uB, max uA uB v, max uA uB v} X (B.Obj X)

set_option linter.checkUnivs false in
/-- In turn, to produce the parametric type `ET`, we must first define a
parametric way of producing for each type `X` the _shape_ type of a
slice polynomial functor, which is a type dependent on `B(X)` -- hence,
a slice over `B`, or equivalently a polynomial functor (coproduct of
representables) on the category of elements of `B`. -/
def ET₁ : Type (max uA uB (v + 1) (w + 1)) := PFSliceCat.Obj.{uA, uB, v, w} B

variable (S : ET₁ B)

end LargeIR

end GebProto
