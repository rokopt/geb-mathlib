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
# The check of the soundness at structural recursion: a clause

The development of the certificate {lit}`datatype-cata-clauses`, of the soundness at a structural
recursion, a clause, checks in the extended program after the statements of the theorems it
continues from, as Lean's evaluator decides. The checks of the developments of the soundness at a
structural recursion are one module to a development, each importing the declarations
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeDeclarations`) and no other check, so that
Lake builds them at the same time. That the developments' theorems are valid in every model of the
program is proved in {lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeValid`.

## Main statements

* {lit}`cataClausesChecked` — the development checks after the theorems it continues from.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeCata

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom cataClausesChecked :
    checkedAfterIn extended3 (·.1.G) upToCata cataClauses = true

end GebTests.Prototypes.FreeTopos.Certified.DatatypeCata

end
