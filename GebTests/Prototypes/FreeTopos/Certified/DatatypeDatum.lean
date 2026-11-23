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
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at datums and decodings, proved in the internal language

The developments of the soundness at a datum and at a decoding of their numbers of elements, each
checked after the statements of the theorems it continues from
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeForms`).

The module imports the developments' declarations
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeDeclarations`) and no other check. That the
developments' theorems are valid in every model of the program is proved in
{lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeValid`.

## Main statements

* {lit}`datumChecked`, {lit}`datumCaseChecked`, {lit}`decodeChecked`, {lit}`decodeCaseChecked` — the
  checks of the developments, which Lean's evaluator decides.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeDatum

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom datumChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeList.decls datum = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom datumCaseChecked :
    checkedAfterIn extended3 (·.1.G) (DatatypeList.decls ++ datum) datumCase = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom decodeChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeForms.upToAssembly decode = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom decodeCaseChecked :
    checkedAfterIn extended3 (·.1.G) (DatatypeForms.upToAssembly ++ datum ++ decode) decodeCase =
      true

end GebTests.Prototypes.FreeTopos.Certified.DatatypeDatum

end
