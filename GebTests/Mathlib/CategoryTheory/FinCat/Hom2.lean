/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Hom2
public import GebTests.Mathlib.CategoryTheory.FinCat.Hom

/-!
# Tests for 2-cell specifications

Three 2-cell specifications out of the terminal category: the one from
the source-picking functor specification into the walking arrow to the
target-picking one, and the two parallel 2-cells on the specification
picking out the idempotent monoid's object. Five assertions exercising
the bundled naturality check, the emptiness of the reverse 2-cell type,
the components of the identity 2-cell and of a vertical composite, and
the component of the generated natural transformation.

Each `natValid` field holds by `rfl`, the naturality quantifier ranging
over the terminal category's empty client range.

## Tags

category, functor, natural transformation, finite category, decidable,
constructive
-/

@[expose] public section

open CategoryTheory

/-- `walkingArrow`'s one non-identity morphism. -/
def arrowMor : walkingArrow.Mor arrowSrc arrowTgt := ⟨0, by decide⟩

/-- The 2-cell from the source-picking functor specification to the
target-picking one, whose single component is that morphism. -/
def arrowPointCell : FinCat.Hom₂ arrowPointSrc arrowPointTgt where
  app := fun _ ↦ arrowMor
  natValid := rfl

/-- The 2-cell on `idemPoint` whose component is the idempotent. -/
def idemCellIdem : FinCat.Hom₂ idemPoint idemPoint where
  app := fun _ ↦ idemMor
  natValid := rfl

/-- The 2-cell on `idemPoint` whose component is the reserved
identity. -/
def idemCellId : FinCat.Hom₂ idemPoint idemPoint where
  app := fun _ ↦ idemIdMor
  natValid := rfl

/-- Assertion 1: the bundled naturality check agrees with the validity
field. -/
theorem arrowPointCell_natCheck : FinCat.Hom₂.natCheck arrowPointCell = true := rfl

/-- Assertion 2: no 2-cell runs the other way. Its component type is
`walkingArrow`'s reverse hom type, which `arrow_homCount_rev` records as
empty. -/
theorem arrowPointRev_isEmpty : IsEmpty (FinCat.Hom₂ arrowPointTgt arrowPointSrc) :=
  ⟨fun α ↦ (α.app termObj).elim0⟩

/-- Assertion 3: the identity 2-cell on the identity specification of
`walkingIso` has the reserved identities as components. -/
theorem isoId_app_id (i : Fin walkingIso.objCount) :
    (𝟙 (FinCat.Hom.id walkingIso) : FinCat.Hom.id walkingIso ⟶ FinCat.Hom.id walkingIso).app i
      = walkingIso.id i := rfl

/-- Assertion 4: and its vertical square has the composites. -/
theorem isoId_app_comp (i : Fin walkingIso.objCount) :
    (𝟙 (FinCat.Hom.id walkingIso) ≫ 𝟙 (FinCat.Hom.id walkingIso)).app i
      = walkingIso.compTotal (walkingIso.id i) (walkingIso.id i) := rfl

/-- Assertion 5: the generated natural transformation's component at the
terminal category's one object is the 2-cell's. -/
theorem arrowPointCell_toNatTrans_app :
    (arrowPointCell.toNatTrans.{0, 0}).app termPoint = ULift.up arrowMor := rfl
