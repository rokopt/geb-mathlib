/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.CategoryTheory.DiscreteFibration
import GebTests.Mathlib.CategoryTheory.DiscreteFibration
import Mathlib.CategoryTheory.Equivalence

/-!
# Tests for the packaged discrete-fibration statements

The example of `GebTests/Mathlib/CategoryTheory/DiscreteFibration.lean`,
against the statements that bundle their content into a mathlib
construction.  Those depend on `Classical.choice`, so these tests do too,
which is why this module is allowlisted and its choice-free sibling is
not.

## Tags

discrete fibration, category of elements
-/

set_option linter.privateModule false

open CategoryTheory

/-- The two formulations of a discrete fibration agree on this example. -/
theorem isDiscreteFibration_iff_constPsh :
    IsDiscreteFibration (Functor.CoElements.π constPsh) ↔
      Nonempty (DiscreteFibration (Functor.CoElements.π constPsh)) :=
  isDiscreteFibration_iff_nonempty

/-- The equivalence between the total category and the category of
elements of its fibre presheaf, on this example. -/
def constElementsEquivalence :
    constPsh.CoElements ≌ constDisc.fiberPresheaf.CoElements :=
  constDisc.elementsEquivalence

/-- The fibre presheaf of the projection is the presheaf, up to the
universe lift. -/
def constFiberPresheafIso :
    (Functor.CoElements.discreteFibration constPsh).fiberPresheaf ≅
      constPsh ⋙ uliftFunctor.{0, 0} :=
  Functor.CoElements.fiberPresheafIso constPsh
