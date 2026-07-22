/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public meta import Batteries.Tactic.Lint.Basic
public meta import Lean.Util.CollectAxioms

/-!
# Axiom-hygiene linter

`detectNonstandardAxiom` is an `@[env_linter]` that fails
`lake lint` when a declaration depends on any axiom outside the
permitted set for its module. For most modules the permitted set
is `{propext, Quot.sound}`; modules in `classicalAllowedModules`
additionally permit `Classical.choice`.

## Main definitions

* `GebMeta.detectNonstandardAxiom` — the linter.
* `GebMeta.classicalAllowedModules` — the exact module names
  additionally permitted to depend on `Classical.choice`.

## Implementation notes

The linter is built on `Lean.collectAxioms` (core Lean, in
`Lean/Util/CollectAxioms.lean`), the same primitive `#print
axioms` uses, and on the `Linter` interface and `@[env_linter]`
attribute of `Batteries/Tactic/Lint/Basic.lean`. The module lives
outside the `Geb`/`GebTests` namespaces so the linter does not
audit its own metaprogramming code.

## Tags

axioms, linter, constructive
-/

public meta section

open Lean Meta Batteries.Tactic.Lint

namespace GebMeta

/-- Axioms a constructive development permits: `propext` and
`Quot.sound`. -/
def standardAxioms : NameSet :=
  (({} : NameSet).insert ``propext).insert ``Quot.sound

/-- Exact module names additionally permitted to depend on
`Classical.choice` (and only `Classical.choice`): the axiom-linter
test fixture, the categorical wrappers over mathlib's
`Classical`-dependent category theory, and the parallel test modules
that exercise those wrappers (a test of a `Classical`-allowed wrapper
is itself `Classical`-dependent). Feature branches append their own
wrapper module names together with their test parallels. -/
def classicalAllowedModules : NameSet :=
  [`GebTests.Internal.AxiomLinterClassicalFixture,
   `Geb.Mathlib.Data.PFunctor.Slice.Functor,
   `Geb.Mathlib.Data.PFunctor.Presheaf.Functor,
   `GebTests.Mathlib.Data.PFunctor.Slice.Functor,
   `GebTests.Mathlib.Data.PFunctor.Presheaf.Functor,
   `Geb.Mathlib.Data.PFunctor.Univariate.Initial,
   `GebTests.Mathlib.Data.PFunctor.Univariate.Initial,
   `Geb.Mathlib.CategoryTheory.Grothendieck,
   `GebTests.Mathlib.CategoryTheory.Grothendieck].foldl (·.insert ·)
    ({} : NameSet)

/-- Permitted axioms for a declaration in module `mod`, given the
allowlist `allowed`: the standard set, plus `Classical.choice` exactly
when `mod` is allowlisted. -/
def permittedAxioms (allowed : NameSet) (mod : Name) : NameSet :=
  let extra := if allowed.contains mod then #[``Classical.choice] else #[]
  extra.foldl (·.insert ·) standardAxioms

/-- The elements of `used` not in the `permitted` set. -/
def offendingAxioms (permitted : NameSet) (used : Array Name) : Array Name :=
  used.filter (!permitted.contains ·)

/-- The defining module of `declName`, if resolvable. Returns `none`
when `getModuleIdxFor?` returns `none` (declaration in the current,
not-yet-imported module) or when the module index is out of range;
both cases route the declaration to the strict axiom set. -/
def moduleOf? (env : Environment) (declName : Name) : Option Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

/-- Flags a declaration depending on an axiom outside its permitted
set. A declaration in a module listed in `classicalAllowedModules`
additionally permits `Classical.choice` (and only that); every other
axiom (`sorryAx`, `Lean.ofReduceBool`, …) is forbidden everywhere. A
declaration whose module is unresolvable is held to the strict set. -/
@[env_linter] def detectNonstandardAxiom : Linter where
  test declName := do
    let mod := (moduleOf? (← getEnv) declName).getD .anonymous
    let permitted := permittedAxioms classicalAllowedModules mod
    let bad := offendingAxioms permitted (← collectAxioms declName)
    if bad.isEmpty then return none
    else return some m!"depends on non-standard axiom(s): {bad.toList}"
  noErrorsFound := "All declarations depend only on permitted axioms."
  errorsFound := "Declarations depend on non-standard axioms."
  isFast := true

end GebMeta
