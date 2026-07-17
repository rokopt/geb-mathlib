/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

@[expose] public section

/-!
# Axiom-linter fixture: a deliberate `Classical.choice` dependency

This module exists to exercise `GebMeta.detectNonstandardAxiom`'s
module-scoped `Classical.choice` allowlist. Its module name is listed
in `GebMeta.classicalAllowedModules`, so the linter accepts the
declaration below despite its `Classical.choice` dependency.
-/

/-- A declaration depending on `Classical.choice` (through
`Classical.em`), used only to test the allowlist. -/
theorem uses_classicalChoice : True :=
  (Classical.em True).elim (fun _ ↦ trivial) (fun _ ↦ trivial)
