/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Basic
public import Geb.Prototypes.MType.Basic

set_option doc.verso true in
/-!
# The cofree-end obstruction

The pointwise cofree construction is an M-type whose nodes carry labels in the positive
parameter. A family of diagonal elements indexed by every type would therefore give an
element of the empty type at its empty-type component. This obstruction holds before
imposing the wedge condition, so taking an end cannot remove it.

## Main definitions

* {lit}`cofreePolynomial` describes a labelled layer.
* {lit}`Cofree` is its M-type, and {lit}`counit` reads the root label.

## Main statements

* {lit}`cofree_family_empty` rules out every diagonal family of cofree trees.

## Tags

polynomial profunctor, M-type, cofree comonad, end
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PHOAS.PProfunctor

universe uA uB uC u v

variable (P : PProfunctor.{uA, uB, uC})

/-- The polynomial for {lit}`Y × P(X, -)`: each node carries a positive label. -/
def cofreePolynomial (X : Type u) (Y : Type v) :
    PFunctor.{max uA v, max uB uC u} :=
  ⟨Y × P.A, fun a ↦ (P.B a.2).Obj X⟩

/-- The carrier of the pointwise cofree comonad, represented by an M-type. -/
abbrev Cofree (X : Type u) (Y : Type v) : Type (max uA uB uC u v) :=
  Geb.MType.M (P.cofreePolynomial X Y)

/-- The counit reads the label at the root of a cofree tree. -/
def counit {X : Type u} {Y : Type v} (t : P.Cofree X Y) : Y := t.head.1

/-- The pointwise greatest fixed-point equation retains the root label. -/
def cofreeUnfold (X : Type u) (Y : Type v) :
    P.Cofree X Y ≃ (Y × P.Obj X (P.Cofree X Y)) :=
  (Geb.MType.M.destEquiv _).trans
    { toFun := fun t ↦ (t.fst.1, .mk t.fst.2 t.snd)
      invFun := fun t ↦ .mk (t.1, t.2.fst) t.2.snd
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- The empty-type component rules out even an incoherent diagonal cofree family. -/
theorem cofree_family_empty (e : (X : Type u) → P.Cofree X X) : False :=
  (P.counit (e PEmpty)).elim

end Geb.PHOAS.PProfunctor
