/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Bicategory
public import GebTests.Mathlib.CategoryTheory.FinCat.Hom2

/-!
# Tests for the strict 2-category of specifications

Five assertions. Three restate the strict unit and associativity laws
through `CategoryTheory.CategoryStruct.comp` and
`CategoryTheory.CategoryStruct.id`, which the `Category FinCat` instance
supplies; each is discharged by the corresponding `FinCat.Hom` theorem,
so together they check that the bicategory's `Hom`, `id` and `comp`
fields agree with `FinCat.Hom`'s. Two compute a whiskering's component
on the fixtures.

Associativity needs three composable 1-cells, and the identity
specifications are the ones the fixtures supply; likewise each
whiskering needs a second 1-cell.

No assertion is made about which `Category FinCat` instance resolves.

## Main statements

* `category_id_comp_arrowPointSrc`, `category_comp_id_arrowPointSrc`,
  `category_assoc_arrowPointSrc` — the strict laws through `≫` and `𝟙`.
* `arrowPointCell_whiskerLeft_app`,
  `arrowPointCell_whiskerRight_app` — the components of the two
  whiskerings of a fixture 2-cell by an identity 1-cell.

## Tags

category, functor, natural transformation, bicategory, 2-category,
whiskering, finite category, decidable, constructive
-/

@[expose] public section

open CategoryTheory

/-- Assertion 1: the identity 1-cell is a left unit, restated through
`≫` and `𝟙` and discharged by the equality of specifications. -/
theorem category_id_comp_arrowPointSrc : 𝟙 terminalCat ≫ arrowPointSrc = arrowPointSrc :=
  FinCat.Hom.id_comp arrowPointSrc

/-- Assertion 2: the identity 1-cell is a right unit, restated through
`≫` and `𝟙` and discharged by the equality of specifications. -/
theorem category_comp_id_arrowPointSrc : arrowPointSrc ≫ 𝟙 walkingArrow = arrowPointSrc :=
  FinCat.Hom.comp_id arrowPointSrc

/-- Assertion 3: composition is associative, at the only triple of
composable 1-cells the fixtures supply. -/
theorem category_assoc_arrowPointSrc :
    (𝟙 terminalCat ≫ arrowPointSrc) ≫ 𝟙 walkingArrow
      = 𝟙 terminalCat ≫ (arrowPointSrc ≫ 𝟙 walkingArrow) :=
  FinCat.Hom.assoc (FinCat.Hom.id terminalCat) arrowPointSrc (FinCat.Hom.id walkingArrow)

/-- Assertion 4: left whiskering reindexes, so whiskering by an identity
1-cell leaves the component unchanged. -/
theorem arrowPointCell_whiskerLeft_app :
    (FinCat.Hom₂.whiskerLeft (FinCat.Hom.id terminalCat) arrowPointCell).app termObj
      = arrowMor := rfl

/-- Assertion 5: right whiskering applies the outer 1-cell's total map,
which for an identity 1-cell is the identity. -/
theorem arrowPointCell_whiskerRight_app :
    (FinCat.Hom₂.whiskerRight arrowPointCell (FinCat.Hom.id walkingArrow)).app termObj
      = arrowMor := rfl
