/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Decidable
public import GebTests.Mathlib.CategoryTheory.FinCat.Hom2

/-!
# Tests for decidable equality

One assertion per level, in both directions: two specifications at the
specification level, two functor specifications at the 1-cell level,
and two 2-cell specifications at the 2-cell level. Each runs the
decision procedure: the negative assertions state a disequality, and
the positive ones state what the procedure returns, so that neither
direction closes by reflexivity of its two sides.

The negative assertions carry the test: a procedure that accepts
everything passes every positive one, and one that rejects everything
passes every negative one. The 2-cell pair is `idemCellIdem` and
`idemCellId`, the only parallel pair any fixture admits, every other
fixture's relevant hom-set being a singleton.

## Tags

category, functor, natural transformation, finite category, decidable
equality, constructive
-/

@[expose] public section

/-- Assertion 1: two specifications agreeing on their object count and
differing in their morphism counts are distinguished. -/
theorem walkingArrow_ne_walkingIso : walkingArrow ≠ walkingIso := by decide

/-- Assertion 2: and the procedure answers affirmatively at a
specification against itself. -/
theorem walkingIso_decide_self : decide (walkingIso = walkingIso) = true := rfl

/-- Assertion 3: two functor specifications differing only in their
object map are distinguished. -/
theorem arrowPointSrc_ne_arrowPointTgt : arrowPointSrc ≠ arrowPointTgt := by decide

/-- Assertion 4: two parallel 2-cell specifications differing in their
one component are distinguished. -/
theorem idemCellIdem_ne_idemCellId : idemCellIdem ≠ idemCellId := by decide

/-- Assertion 5: and affirmatively at a 2-cell specification against
itself. -/
theorem idemCellIdem_decide_self : decide (idemCellIdem = idemCellIdem) = true := rfl
