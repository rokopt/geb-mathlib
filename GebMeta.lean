/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public meta import Batteries.Tactic.Lint.Basic
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.ElabRules

/-!
# Axiom-hygiene linter and mathlib linter options

`detectNonstandardAxiom` is an `@[env_linter]` that fails
`lake lint` when a declaration depends on any axiom outside the
permitted set for its module. For most modules the permitted set
is `{propext, Quot.sound}`; modules in `classicalAllowedModules`
additionally permit `Classical.choice`. `mathlib_linters` is a
command that sets two of mathlib's registered linter options in
the invoking file's scope, for a library whose Lake options
cannot carry them.

## Main definitions

* `GebMeta.detectNonstandardAxiom` — the linter.
* `GebMeta.classicalAllowedModules` — the exact module names
  additionally permitted to depend on `Classical.choice`.
* `GebMeta.mathlibLinterOptions` — the linter options
  `mathlib_linters` sets.
* `mathlib_linters` — the command that sets
  `mathlibLinterOptions` in the invoking file's scope.

## Implementation notes

The linter is built on `Lean.collectAxioms` (core Lean, in
`Lean/Util/CollectAxioms.lean`), the same primitive `#print
axioms` uses, and on the `Linter` interface and `@[env_linter]`
attribute of `Batteries/Tactic/Lint/Basic.lean`. The module lives
outside the `Geb`, `GebTests` and `GebLang` namespaces so the linter
does not audit its own metaprogramming code.

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
`Classical.choice` (and only `Classical.choice`): a module with no
choice-free content of its own left to state, either because it is a
wrapper whose content is packaging or because its subject is the
correspondence between a concept developed here and a concept of an
external Lean library (Batteries, mathlib, CSLib) that itself uses
`Classical.choice`; the `GebTests` parallel of such a module (a test of a
`Classical`-allowed module is itself `Classical`-dependent); and the
axiom-linter's own test fixture. Feature branches append the module names
their own such modules occupy. -/
def classicalAllowedModules : NameSet :=
  [`GebTests.Prototypes.AxiomLinterClassicalFixture,
   `Geb.Prototypes.PresheafIRProto.Functor,
   `Geb.Mathlib.Data.PFunctor.Slice.Functor,
   `Geb.Mathlib.Data.PFunctor.Presheaf.Functor,
   `GebTests.Mathlib.Data.PFunctor.Slice.Functor,
   `GebTests.Mathlib.Data.PFunctor.Presheaf.Functor,
   `Geb.Mathlib.Data.PFunctor.Univariate.Initial,
   `GebTests.Mathlib.Data.PFunctor.Univariate.Initial,
   `Geb.Mathlib.CategoryTheory.DiscreteFibration.Packaged,
   `GebTests.Mathlib.CategoryTheory.DiscreteFibration.Packaged,
   `Geb.Mathlib.CategoryTheory.Grothendieck,
   `GebTests.Mathlib.CategoryTheory.Grothendieck,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Skeleton,
   `Geb.Mathlib.CategoryTheory.ElementaryTopos,
   `GebTests.Mathlib.CategoryTheory.ElementaryTopos,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Coequalizer,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Coequalizer,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Exponential.Closed,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Exponential.Closed,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Limits,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Limits,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Classifier.Instance,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Classifier.Instance,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.ElementaryTopos,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.ElementaryTopos,
   `Geb.Mathlib.CategoryTheory.FinCat.FinCategory,
   `GebTests.Mathlib.CategoryTheory.FinCat.FinCategory,
   `Geb.Prototypes.Computability.TreeScanner.Steps,
   `Geb.Prototypes.Computability.TreeScanner.Bound,
   `GebTests.Prototypes.Computability.TreeScanner.Machine].foldl (·.insert ·)
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
@[env_linter] def detectNonstandardAxiom : Batteries.Tactic.Lint.Linter where
  test declName := do
    let mod := (moduleOf? (← getEnv) declName).getD .anonymous
    let permitted := permittedAxioms classicalAllowedModules mod
    let bad := offendingAxioms permitted (← collectAxioms declName)
    if bad.isEmpty then return none
    else return some m!"depends on non-standard axiom(s): {bad.toList}"
  noErrorsFound := "All declarations depend only on permitted axioms."
  errorsFound := "Declarations depend on non-standard axioms."
  isFast := true

/-- The linter options `mathlib_linters` sets. mathlib registers these, so
they are set and ignored in a module with no mathlib in its import closure.
`linter.style.header` is absent: it acts only on commands ending at or before
a file's first module docstring, and its own check requires that docstring to
be the first command after the imports, so a command placed to satisfy that
check runs too late to enable it. -/
def mathlibLinterOptions : List Name :=
  [`linter.mathlibStandardSet, `linter.flexible]

/-- Sets `mathlibLinterOptions` in the invoking file, from the invocation
onward.

A library whose docstrings Verso's literate pipeline renders cannot carry
these in its Lake options: the pipeline's module facet re-serialises a
module's Lean options as `-D` arguments to an executable that rejects a name
it does not register, and it parses those arguments before it loads the
module, so the module's own imports do not help. Options set in a scope are
not part of a module's Lake options and never reach it. -/
syntax "mathlib_linters" : command

elab_rules : command
  | `(mathlib_linters) => do
    Lean.Elab.Command.modifyScope fun s =>
      { s with opts := mathlibLinterOptions.foldl (fun o n => o.setBool n true) s.opts }

end GebMeta
