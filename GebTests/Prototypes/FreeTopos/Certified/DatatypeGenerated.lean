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
public meta import GebTests.Prototypes.FreeTopos.DatatypeConstructor -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The definitions the datatype language generates, proved in the internal language

The recognizers and the constructors the expansion of the datatype language writes: the developments
of what the writer's forms denote, of the recognizers' decisions and of the constructors'
definitions, each checked after the statements of the theorems it continues from, in the order of
its certificate's search ({lit}`GebTests.Prototypes.FreeTopos.Certificates`).

The module imports the developments' declarations
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeDeclarations`) and no other check. That the
developments' theorems are valid in every model of the program is proved in
{lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeValid`.

## Main statements

* {lit}`denChecked`, {lit}`walkChecked`, {lit}`recognizerChecked`, {lit}`recognizerFoldChecked`,
  {lit}`ctorChecked`, {lit}`ctorBodyChecked`, {lit}`ctorLamChecked`, {lit}`ctorNestChecked` — the
  checks of the developments, which Lean's evaluator decides.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeGenerated

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom denChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeCase.upToCase den = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom walkChecked :
    checkedAfterIn extended3 (·.1.G) upToWalkBase walk = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom recognizerChecked :
    checkedAfterIn extended3 (·.1.G) upToWalk recognizer = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom recognizerFoldChecked :
    checkedAfterIn extended3 (·.1.G) upToRecognizer recognizerFold = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom ctorChecked :
    checkedAfterIn extended3 (·.1.G) upToRecognizerFold ctor = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom ctorBodyChecked :
    checkedAfterIn extended3 (·.1.G) upToCtor ctorBody = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom ctorLamChecked :
    checkedAfterIn extended3 (·.1.G) upToCtorBody ctorLam = true

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom ctorNestChecked :
    checkedAfterIn extended3 (·.1.G) upToCtorLam ctorNest = true

end GebTests.Prototypes.FreeTopos.Certified.DatatypeGenerated

end
