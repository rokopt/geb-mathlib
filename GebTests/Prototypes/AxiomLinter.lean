/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
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

## Tags

axioms, linter, constructive
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

/-- A local dependency on `propext`, for the stop test below: the bodies
of this module's own declarations are loaded whatever the context. -/
theorem stopFixture : (True ∧ True) = True :=
  propext ⟨fun h ↦ h.1, fun h ↦ ⟨h, h⟩⟩

/-- A declaration reaching `propext` only through `stopFixture`. -/
theorem viaStopFixture : (True ∧ True) = True := stopFixture

-- Collection stops at a listed constant and nowhere else: `propext` is
-- reported beneath `viaStopFixture` unless collection stops at
-- `stopFixture`, and a stop elsewhere leaves it reported.
open Lean Elab Command in
run_cmd do
  let check (stops : List Name) (expected : Bool) : CommandElabM Unit := do
    let cache ← IO.mkRef {}
    let axs ← liftCoreM <| collectAxiomsStopping (NameSet.ofList stops) cache ``viaStopFixture
    unless axs.contains ``propext == expected do
      throwError "stops {stops}: expected propext reported = {expected}, got {axs}"
  check [] true
  check [``stopFixture] false
  check [``Classical.em] true

-- Module resolution returns a module for an imported declaration.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless (GebMeta.moduleOf? env ``propext).isSome do
    throwError "moduleOf? failed to resolve the imported declaration `propext`"
