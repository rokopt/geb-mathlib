/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Presheaf.Basic
public import Mathlib.CategoryTheory.Category.Preorder

set_option doc.verso true in
/-!
# A point over each natural number

Over the natural numbers ordered as a category, the signature with one operation without
arguments over each number, the point, whose restriction along {lit}`m ≤ n` is the point over
{lit}`m`. With no further equations, the presentation's classes form a presheaf, and the equation
of naturality makes the restriction of the class of a point the class of the restricted point.

## Main definitions

* {lit}`pointSig` — the signature.
* {lit}`points` — the presentation without further equations.

## Main statements

* {lit}`restrCls_point` — the restriction of the class of a point is the class of the point below.

## Tags

presheaf, equational presentation, restriction, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.PresheafTests

open CategoryTheory PFunctor GebProto Geb.Definition.Slice Geb.Definition.Presheaf

/-- One point over each natural number, restricting to the point below. -/
def pointSig : Sig.{0} ℕ where
  A := ℕ
  q n := n
  Gen _ := PEmpty
  gobj _ x := nomatch x
  restr _ {m} _ := m
  q_restr _ _ _ := rfl
  reindex _ _ _ x := nomatch x

/-- The empty equation functor. -/
def noEqns : SlicePFunctor.{0, 0, 0, 0} ℕ ℕ where
  A := PEmpty
  B x := nomatch x
  r x := nomatch x.1
  q x := nomatch x

/-- The presentation of the points without further equations. -/
def points : Presheaf.Presentation.{0, 0} pointSig where
  E := noEqns
  lhs x := nomatch x
  rhs x := nomatch x
  lhs_sorted x := nomatch x
  rhs_sorted x := nomatch x

/-- The closed terms have no variables. -/
abbrev noVars : PEmpty.{1} → ℕ := PEmpty.elim

/-- The point over {lit}`n`, as a closed term. -/
def pointTm (n : ℕ) : Tm (ops pointSig) noVars n :=
  opTm (F := ops pointSig) noVars (.inl n) fun x ↦ nomatch x

/-- The restriction of the class of a point is the class of the point below. -/
theorem restrCls_point {m n : ℕ} (h : m ≤ n) :
    points.restrCls noVars (homOfLE h) (points.toSlice.cls noVars (pointTm n)) =
      points.toSlice.cls noVars (pointTm m) := by
  refine (points.restrCls_cls noVars (homOfLE h) (pointTm n)).trans
    ((congrArg (points.toSlice.cls noVars) (Subtype.ext ?_)).trans
      ((points.toSlice.cls_bind_lhs noVars (.inl (.nat n (homOfLE h))) (fun x ↦ nomatch x)
        fun x ↦ nomatch x).trans (congrArg (points.toSlice.cls noVars) (Subtype.ext ?_))))
  · exact congrArg (FreeM.liftBind (P := (ops pointSig).toPFunctor) (.inr ⟨n, m, homOfLE h⟩))
      (funext fun _ ↦ congrArg (FreeM.liftBind (P := (ops pointSig).toPFunctor) (.inl n))
        (funext fun x ↦ nomatch x))
  · exact congrArg (FreeM.liftBind (P := (ops pointSig).toPFunctor) (.inl m))
      (funext fun x ↦ nomatch x)

example : (points.clsPsh noVars).map (homOfLE (show 1 ≤ 2 by omega)).op
    (points.toSlice.cls noVars (pointTm 2)) = points.toSlice.cls noVars (pointTm 1) :=
  restrCls_point _

end Geb.Definition.PresheafTests

end
