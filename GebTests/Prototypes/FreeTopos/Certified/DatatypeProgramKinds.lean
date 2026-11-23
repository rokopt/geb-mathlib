/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeDeclarations
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeDeclarations -- shake: keep
public import GebTests.Prototypes.FreeTopos.DatatypeBase
public meta import GebTests.Prototypes.FreeTopos.DatatypeBase -- shake: keep
public import GebTests.Prototypes.ProgramCommand
public import GebTests.Prototypes.FreeTopos.Certified.Chain
public meta import GebTests.Prototypes.FreeTopos.Certified.Chain -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The steps of a whole program's soundness at definitions, proved in the internal language

The developments of the invariant of a whole program's soundness and of its steps at the forms
that write a definition, a type or a numeral abbreviation, and at a template's instance, each
checked after the theorems of those before it, in the order of their search
({lit}`GebTests.Prototypes.FreeTopos.Certificates`).

The module imports the developments' declarations
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeDeclarations`) and no other check. That the
developments' theorems are valid in every model of the program is proved in
{lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeValid`.

## Main statements

* {lit}`kindsChecked` — the checks of the developments, which Lean's evaluator decides.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramKinds

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

set_option doc.verso false in
/-- Each of the developments checks in the extended program, after the theorems of those it
continues from and of those before it, as Lean's evaluator decides. -/
evaluation_axiom kindsChecked :
    checkedChainIn extended3 (·.1.G) kinds DatatypeProgram.upToRuns = true

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramKinds

end
