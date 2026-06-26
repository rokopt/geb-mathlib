/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import Geb.Mathlib.Data.PFunctor.Slice.Basic

-- Test files keep their declarations private; silence the
-- only-private-declarations lint.
set_option linter.privateModule false

/-!
# Tests for the slice polynomial functor core
-/

open SliceDomPFunctor SlicePFunctor

/-- A concrete slice polynomial functor: one shape, two `Bool`-indexed
positions, constraint `s ⟨(), b⟩ = b`, tag into `Unit`. -/
def testSlice : SlicePFunctor Bool Unit where
  A := Unit
  B := fun _ => Bool
  s := fun x => x.2
  t := fun _ => ()

example : testSlice.s ⟨(), true⟩ = true := rfl
example : testSlice.t () = () := rfl

example (X : Type) (p : X → Bool) (v : Bool → X) :
    testSlice.Compatible p () v ↔ ∀ b, p (v b) = b :=
  testSlice.compatible_iff p () v
