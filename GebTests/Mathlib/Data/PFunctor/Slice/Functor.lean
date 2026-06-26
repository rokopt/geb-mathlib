/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module -- shake: keep-all

import Geb.Mathlib.Data.PFunctor.Slice.Functor

set_option linter.privateModule false

/-!
# Tests for the slice polynomial functor wrapper
-/

open CategoryTheory SliceDomPFunctor SlicePFunctor

/-- A concrete slice polynomial functor for the wrapper tests (local,
to avoid a cross-test-file dependency). -/
def wrapperTestSlice : SlicePFunctor Bool Unit where
  A := Unit
  B := fun _ => Bool
  s := fun x => x.2
  t := fun _ => ()

-- The slice-valued functor forgets back to `domFunctor`.
example : wrapperTestSlice.functor ⋙ Over.forget Unit =
    wrapperTestSlice.toSliceDomPFunctor.domFunctor :=
  wrapperTestSlice.functor_comp_forget
