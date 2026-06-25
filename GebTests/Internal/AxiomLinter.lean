/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module -- shake: keep-all
public meta import Lean.Elab.Command
public import Lean.Exception
import GebMeta

/-!
# Unit tests for `GebMeta` axiom-hygiene helpers

Example-based checks of the pure axiom classifier behind the
`detectNonstandardAxiom` linter, plus allowlist-logic unit tests
and a module-resolution meta-test.
-/

open Lean GebMeta

-- The standard axioms are accepted (none offending).
#guard offendingAxioms standardAxioms #[``propext, ``Quot.sound] == #[]

-- A non-standard axiom is reported.
#guard offendingAxioms standardAxioms #[``propext, ``Classical.choice, ``Quot.sound]
  == #[``Classical.choice]

-- `sorryAx` is reported.
#guard offendingAxioms standardAxioms #[``sorryAx] == #[``sorryAx]

-- `permittedAxioms`: a non-allowlisted module gets the strict set.
#guard !((permittedAxioms ({} : NameSet) `Some.Module).contains ``Classical.choice)

-- `permittedAxioms`: an allowlisted module additionally permits
-- `Classical.choice`, and nothing else.
#guard (permittedAxioms (({} : NameSet).insert `Some.Module) `Some.Module).contains
  ``Classical.choice
#guard !((permittedAxioms (({} : NameSet).insert `Some.Module) `Some.Module).contains
  ``sorryAx)

-- Under the permissive set: `Classical.choice` is allowed, but
-- `sorryAx` remains offending (the "did not widen too far" assertion).
#guard offendingAxioms (standardAxioms.insert ``Classical.choice) #[``Classical.choice]
  == #[]
#guard offendingAxioms (standardAxioms.insert ``Classical.choice) #[``sorryAx]
  == #[``sorryAx]
#guard offendingAxioms (standardAxioms.insert ``Classical.choice)
  #[``Classical.choice, ``sorryAx] == #[``sorryAx]

-- Module resolution returns a module for an imported declaration.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless (GebMeta.moduleOf? env ``propext).isSome do
    throwError "moduleOf? failed to resolve the imported declaration `propext`"
