/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.ParanaturalRank

/-!
# Tests for the separation of strong dinaturality from parametricity

The two sides of the separating instance computed: the endomorphism pair the
twisted hypothesis reaches, the identity pair it does not, and the two values
`selfApply` takes at the instance where it fails to be strongly dinatural.

## Tags

prototype, paranatural, strong dinaturality, parametricity, reduction test
-/

open GebProto.ParanaturalRank

/-! ## The two endomorphism pairs

The one function `Bool → Unit` produces the constant map at `true`, on which
`qBool` agrees with the value the twisted hypothesis needs; the identity, which
`jUnitBool` intertwines with itself, is where the free theorem's hypothesis asks
for the same value and does not get it. -/

example : qBool (jUnitBool ∘ (fun _ ↦ ())) = true := rfl

example : qBool _root_.id = false := rfl

example : jUnitBool (pUnit _root_.id) = true := rfl

/-! ## The term the twisted condition excludes -/

/-- The value `selfApply` takes at the separating instance. -/
def selfApplyBool : Bool := selfApply Bool qBool

example : selfApplyBool = false := rfl

example : jUnitBool (selfApply Unit pUnit) = true := rfl
