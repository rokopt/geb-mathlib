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
# The passes' runs over a program's forms, proved in the internal language

The developments the soundness of a whole program of the datatype language continues from, and
those of the runs of the compiler's passes over a program's forms: the typing's runs, checked
after the base's theorems, and the runs of the expansion, the reader and the kernel's check with
the invariants the reading of a definition preserves, each checked after the theorems of those
before it, in the order of their search ({lit}`GebTests.Prototypes.FreeTopos.Certificates`).

The module imports the developments' declarations
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeDeclarations`) and no other check. That the
developments' theorems are valid in every model of the program is proved in
{lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeValid`.

## Main statements

* {lit}`programChecked`, {lit}`runsChecked` — the checks of the developments, which Lean's evaluator
  decides.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgram

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

set_option doc.verso false in
/-- The development checks in the extended program, after the base's theorems, as Lean's
evaluator decides. -/
evaluation_axiom programChecked :
    checkedAfterIn extended3 (·.1.G) base program = true

set_option doc.verso false in
/-- Each of the developments checks in the extended program, after the theorems of those it
continues from and of those before it, as Lean's evaluator decides. -/
evaluation_axiom runsChecked :
    checkedChainIn extended3 (·.1.G) runs before = true

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgram

end
