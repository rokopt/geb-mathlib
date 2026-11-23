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
public import GebTests.Prototypes.FreeTopos.DatatypeProgramStep
public meta import GebTests.Prototypes.FreeTopos.DatatypeProgramStep -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a whole program, proved in the internal language

The soundness of a whole program of the datatype language's stage-1 compiler: the developments
of the kinds of forms, of the induction on a program's forms and of the program's soundness,
each checked after the theorems of those before it, in the order of their search
({lit}`GebTests.Prototypes.FreeTopos.Certificates`).

The module imports the developments' declarations
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeDeclarations`) and no other check. That the
developments' theorems are valid in every model of the program is proved in
{lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeValid`.

## Main statements

* {lit}`defsChecked`, {lit}`soundChecked`, {lit}`soundStates`, {lit}`closedChecked`,
  {lit}`closedStates` — the checks of the developments, which Lean's evaluator decides.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramSound

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as
Lean's evaluator decides. -/
evaluation_axiom defsChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeProgramData.upToData defs = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as
Lean's evaluator decides. -/
evaluation_axiom soundChecked :
    checkedAfterIn extended3 (·.1.G) upToDefs sound = true

/-- The statement of a program's soundness in a program ({name}`programFormsThm`), and a
statement without hypotheses where its parts are not given. -/
def soundThm (PST : Prog × Defs × Defs3) : Internal.Thm :=
  (programFormsThm PST.1 PST.2.1 PST.2.2).getD ⟨0, [], [], Internal.Term.star⟩

set_option doc.verso false in
/-- The development's last declaration states the soundness of a program, as Lean's evaluator
decides. -/
evaluation_axiom soundStates : statesLastIn extended3 sound soundThm = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as
Lean's evaluator decides. -/
evaluation_axiom closedChecked :
    checkedAfterIn extended3 (·.1.G) upToSound closed = true

/-- The statement of a program's soundness as one formula in a program
({name}`programClosedThm`), and a statement without hypotheses where its parts are not
given. -/
def closedThm (PST : Prog × Defs × Defs3) : Internal.Thm :=
  (programClosedThm PST.1 PST.2.1 PST.2.2).getD ⟨0, [], [], Internal.Term.star⟩

set_option doc.verso false in
/-- The development's last declaration states the soundness of a program as one formula, as
Lean's evaluator decides. -/
evaluation_axiom closedStates : statesLastIn extended3 closed closedThm = true

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramSound

end
