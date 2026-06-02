/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public meta import Lean.Util.CollectAxioms
public meta import Batteries.Tactic.Lint.Basic

/-!
# Axiom-hygiene linter

`detectNonstandardAxiom` is an `@[env_linter]` that fails
`lake lint` when a declaration depends on any axiom outside the
constructive standard set `{propext, Quot.sound}`. It is built on
`Lean.collectAxioms` (core Lean), the same primitive `#print
axioms` uses. The module lives outside the `Geb`/`GebTests`
namespaces so the linter does not audit its own metaprogramming
code.

## References

- `Lean/Util/CollectAxioms.lean` (core Lean) — `collectAxioms`.
- `Batteries/Tactic/Lint/Basic.lean` — the `Linter` interface and
  the `@[env_linter]` attribute.
-/

public meta section

open Lean Meta Batteries.Tactic.Lint

namespace GebMeta

/-- Axioms a constructive development permits: `propext` and
`Quot.sound`. -/
def standardAxioms : NameSet :=
  (({} : NameSet).insert ``propext).insert ``Quot.sound

/-- The elements of `used` that are not standard axioms. -/
def offendingAxioms (used : Array Name) : Array Name :=
  used.filter (fun a => !standardAxioms.contains a)

/-- Flags a declaration depending on a non-standard axiom
(anything outside `{propext, Quot.sound}`, e.g. `Classical.choice`,
`sorryAx`, `Lean.ofReduceBool`). -/
@[env_linter] def detectNonstandardAxiom : Linter where
  test declName := do
    let bad := offendingAxioms (← collectAxioms declName)
    if bad.isEmpty then return none
    else return some m!"depends on non-standard axiom(s): {bad.toList}"
  noErrorsFound := "All declarations depend only on propext and Quot.sound."
  errorsFound := "Declarations depend on non-standard axioms."
  isFast := true

end GebMeta
