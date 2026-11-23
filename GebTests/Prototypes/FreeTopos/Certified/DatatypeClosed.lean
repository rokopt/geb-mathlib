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
public import GebTests.Prototypes.FreeTopos.DatatypeClosed
public meta import GebTests.Prototypes.FreeTopos.DatatypeClosed -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at every tree, proved in the internal language

The soundness of the datatype language's stage-1 compiler at every tree, without hypotheses: the
development of the discharge of the keywords the soundness at every tree takes as hypotheses,
checked after the statements of the theorems it continues from, in the order of its certificate's
search ({lit}`GebTests.Prototypes.FreeTopos.Certificates`).

The module imports the developments' declarations
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeDeclarations`) and no other check. That the
developments' theorems are valid in every model of the program is proved in
{lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeValid`.

## Main statements

* {lit}`closedChecked`, {lit}`closedStates` — the checks of the developments, which Lean's evaluator
  decides.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeClosed

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom closedChecked :
    checkedAfterIn extended3 (·.1.G) before closed = true

set_option doc.verso false in
/-- The development's last declaration states the soundness at every tree without hypotheses, as
Lean's evaluator decides. -/
evaluation_axiom closedStates :
    statesLastIn extended3 closed (fun PST ↦ soundClosedThm PST.1 PST.2.1 PST.2.2) = true

end GebTests.Prototypes.FreeTopos.Certified.DatatypeClosed

end
