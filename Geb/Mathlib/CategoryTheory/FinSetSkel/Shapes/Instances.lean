/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Core
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The cartesian and coproduct structure of `FinSetSkel`

The mathlib packaging of `Shapes/Core.lean`'s rows a, b, c and d: the
chosen cones, the `CartesianMonoidalCategory` instance built from
them, and the `Prop` instances a later workstream consumes.
`CartesianMonoidalCategory` depends on `Classical.choice`, so this
module is allowlisted and the constructions it packages are not.

`CartesianMonoidalCategory.ofChosenFiniteProducts` takes a terminal
cone and a family of binary product cones and supplies the
associator, the unitors and the coherence conditions, so no
monoidal law is proved here. Its instance registers
`HasFiniteProducts`, `HasTerminal` and `HasBinaryProducts` at
priority 100, so none of the three is registered separately.

## Main definitions

* `FinSetSkel.terminalCone`, `FinSetSkel.binaryProductCone`,
  `FinSetSkel.initialCocone`, `FinSetSkel.binaryCoproductCocone` —
  the chosen cones.
* `FinSetSkel.cartesianMonoidalCategory` — the cartesian structure.
* `FinSetSkel.isTerminalOne` — the one-element object is terminal.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, cartesian, coproduct, topos
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace FinSetSkel

/-- The chosen terminal cone: the one-element object. -/
def terminalCone : LimitCone (Functor.empty.{0} FinSetSkel.{u}) where
  cone := asEmptyCone (mk 1)
  isLimit := IsTerminal.ofUniqueHom (fun X ↦ toOne X) (fun _ f ↦ toOne_uniq f)

/-- The chosen binary product cone. -/
def binaryProductCone (X Y : FinSetSkel.{u}) : LimitCone (pair X Y) where
  cone := BinaryFan.mk (prodFst X Y) (prodSnd X Y)
  isLimit :=
    BinaryFan.IsLimit.mk _ (fun f g ↦ prodLift f g)
      (fun f g ↦ prodLift_fst f g) (fun f g ↦ prodLift_snd f g)
      (fun f g m hf hg ↦ prodLift_uniq f g m hf hg)

/-- The cartesian monoidal structure, from the chosen terminal cone
and the chosen binary product cones. -/
instance cartesianMonoidalCategory :
    CartesianMonoidalCategory FinSetSkel.{u} :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalCone
    binaryProductCone

/-- The one-element object is terminal. -/
def isTerminalOne : IsTerminal (mk 1 : FinSetSkel.{u}) :=
  SemiCartesianMonoidalCategory.isTerminalTensorUnit

end FinSetSkel
