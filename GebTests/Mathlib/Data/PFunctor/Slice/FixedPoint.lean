/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Slice.FixedPoint

/-!
# Tests for fixed points of slice endofunctors

The W-type's fixed point unfolds to the W-type's carrier, structure map,
constructor and destructor, and its constructor lies over the index.

## Tags

fixed point, W-type, slice category
-/

set_option linter.privateModule false

open SlicePFunctor

-- The W-type's fixed point has the W-type's carrier and structure map.
example (F : SlicePFunctor.{0, 0} Bool Bool) : F.wFixedPoint.T = F.W := rfl
example (F : SlicePFunctor.{0, 0} Bool Bool) : F.wFixedPoint.index = F.wIndex := rfl

/-- The constructor lies over `I`, from the generic fixed-point law at the
W-type: a named value, so that `lake shake` observes the import. -/
theorem wFixedPoint_index_mk (F : SlicePFunctor.{0, 0} Bool Bool)
    (x : F.toSliceDomPFunctor.Obj F.wIndex) : F.wIndex (W.mk x) = F.obj F.wIndex x :=
  F.wFixedPoint.index_mk x
