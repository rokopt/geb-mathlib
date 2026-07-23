/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Univariate.Finitary

/-!
# Tests for `PFunctor.Finitary`

`[P.Finitary]` resolves both a `FinEnum` and, through its `decEq` field,
a `DecidableEq` on the directions of a shape.

## Tags

polynomial functor, PFunctor, finitary, FinEnum
-/

set_option linter.privateModule false

/-- `[P.Finitary]` supplies the direction enumeration. -/
@[instance_reducible]
def finitaryGivesFinEnum (P : PFunctor.{0, 0}) [P.Finitary] (a : P.A) :
    FinEnum (P.B a) := inferInstance

/-- `[P.Finitary]` supplies decidable equality of directions, through
`FinEnum`'s `decEq` field. -/
@[instance_reducible]
def finitaryGivesDecEq (P : PFunctor.{0, 0}) [P.Finitary] (a : P.A) :
    DecidableEq (P.B a) := inferInstance
