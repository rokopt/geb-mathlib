/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.W
import GebTests.Mathlib.Data.PFunctor.Presheaf.Fixtures

/-!
# Tests for carrier presheaves

At the shared walking-arrow fixture, the presheaf W-type is the generic carrier
presheaf of the slice W-type with its hereditary naturality, its restriction is
the generic root restriction, and the generic fixed-point laws hold at it.

## Tags

polynomial functor, presheaf, fixed point, W-type
-/

set_option linter.privateModule false

open CategoryTheory PresheafPFunctor PresheafFixture

-- The presheaf W-type is the generic carrier presheaf.
example : wFixture.W = wFixture.carrier wFixture.wHereditaryNaturality := rfl

-- Its root restriction is the generic one at the W-type's fixed point.
example ⦃j j' : Fin 2⦄ (g : j' ⟶ j) (z : wFixture.toSlicePFunctor.W)
    (hq : wFixture.q (PFunctor.W.head z.1) = j) :
    wFixture.wRestrTree g z hq = wFixture.restrTree wFixture.toSlicePFunctor.wFixedPoint g z hq :=
  rfl

/-- Restriction along an identity fixes the good tree of the fixture: a named
value, so that `lake shake` observes the imports. -/
theorem goodTree_restrTree_id :
    wFixture.restrTree wFixture.toSlicePFunctor.wFixedPoint (𝟙 1) goodTree rfl = goodTree :=
  wFixture.restrTree_id wFixture.toSlicePFunctor.wFixedPoint (j := 1) goodTree rfl

-- The generic constructor and destructor are mutually inverse at the fixture.
example {j : Fin 2} (x : (wFixture.objPresheaf wFixture.W).obj ⟨j⟩) :
    carrier.dest (carrier.mk (N := wFixture.wHereditaryNaturality) x) = x :=
  carrier.dest_mk x
