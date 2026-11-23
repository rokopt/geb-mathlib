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
# The datatype language's soundness given the later keywords', proved in the internal language

The developments of the applications, the abstractions, the representations, the kernel's constants
and every list, stored in the certificates of {lit}`bootstrap/certificates/` that continue from the
keywords' forms' ({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeList`). Each is checked
after the statements of the theorems it continues from, and its theorems are valid in every model of
the program in which those are, so that a check reads no derivation of another development.

The module imports the developments' declarations
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeDeclarations`) and no other check. That the
developments' theorems are valid in every model of the program is proved in
{lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeValid`.

## Main statements

* {lit}`stagesChecked`, {lit}`applyChecked`, {lit}`expansionChecked`, {lit}`assemblyChecked`,
  {lit}`appChecked`, {lit}`lamChecked`, {lit}`dataChecked`, {lit}`foldsChecked`,
  {lit}`listsChecked`, {lit}`soundChecked` — the checks of the developments, which Lean's evaluator
  decides.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeForms

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom stagesChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeList.decls stages = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom applyChecked :
    checkedAfterIn extended3 (·.1.G) upToStages apply = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom expansionChecked :
    checkedAfterIn extended3 (·.1.G) upToApply expansion = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom assemblyChecked :
    checkedAfterIn extended3 (·.1.G) upToExpansion assembly = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom appChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeList.decls app = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom lamChecked :
    checkedAfterIn extended3 (·.1.G) (DatatypeList.decls ++ app ++ stages) lam = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom dataChecked :
    checkedAfterIn extended3 (·.1.G) upToAssembly data = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom foldsChecked :
    checkedAfterIn extended3 (·.1.G) upToAssembly folds = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom listsChecked :
    checkedAfterIn extended3 (·.1.G) upToFolds lists = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom soundChecked :
    checkedAfterIn extended3 (·.1.G) (upToFolds ++ lists) sound = true

end GebTests.Prototypes.FreeTopos.Certified.DatatypeForms

end
