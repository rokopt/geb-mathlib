/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module -- shake: keep-all

import GebMeta

/-!
# Unit tests for `GebMeta.offendingAxioms`

Example-based checks of the pure axiom classifier behind the
`detectNonstandardAxiom` linter.
-/

open GebMeta

-- The standard axioms are accepted (none offending).
#guard offendingAxioms #[``propext, ``Quot.sound] == #[]

-- A non-standard axiom is reported.
#guard offendingAxioms #[``propext, ``Classical.choice, ``Quot.sound]
  == #[``Classical.choice]

-- `sorryAx` is reported.
#guard offendingAxioms #[``sorryAx] == #[``sorryAx]
