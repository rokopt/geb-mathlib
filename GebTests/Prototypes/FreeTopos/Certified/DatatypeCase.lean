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
# The datatype language's soundness at case analysis, proved in the internal language

The developments of the soundness at a case analysis: the walk of a clause's fields, the chain of
its clauses and the source form, each checked after the statements of the theorems it continues from
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeDatum`).

The module imports the developments' declarations
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeDeclarations`) and no other check. That the
developments' theorems are valid in every model of the program is proved in
{lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeValid`.

## Main statements

* {lit}`caseDevChecked`, {lit}`clausesChecked`, {lit}`caseSoundChecked` — the checks of the
  developments, which Lean's evaluator decides.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeCase

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom caseDevChecked :
    checkedAfterIn extended3 (·.1.G) upToFolds caseDev = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom clausesChecked :
    checkedAfterIn extended3 (·.1.G) upToCase clauses = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom caseSoundChecked :
    checkedAfterIn extended3 (·.1.G) upToClauses caseSound = true

end GebTests.Prototypes.FreeTopos.Certified.DatatypeCase

end
