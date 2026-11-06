/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCase
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeCase -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeConstructor -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The definitions the datatype language generates, proved in the internal language

The recognizers and the constructors the expansion of the datatype language writes: the developments
of what the writer's forms denote, of the recognizers' decisions and of the constructors'
definitions, each checked after the statements of the theorems it continues from, in the order of
its certificate's search ({lit}`GebTests.Prototypes.FreeTopos.Certificates`).

## Main statements

* {lit}`upToCtorNest_valid` — the theorems of the developments are valid in every model of the
  program.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeGenerated

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

/-- The development of the certificate {lit}`datatype-den`. -/
def den : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-den.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom denChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeCase.upToCase den = true

/-- The developments the walk of a constructor's fields continues from. -/
def upToWalkBase : List Internal.Decl := DatatypeCase.upToCaseSound ++ den

/-- The development of the certificate {lit}`datatype-walk`. -/
def walk : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-walk.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom walkChecked :
    checkedAfterIn extended3 (·.1.G) upToWalkBase walk = true

/-- With the walk of a constructor's fields. -/
def upToWalk : List Internal.Decl := upToWalkBase ++ walk

/-- The development of the certificate {lit}`datatype-recognizer`. -/
def recognizer : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-recognizer.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom recognizerChecked :
    checkedAfterIn extended3 (·.1.G) upToWalk recognizer = true

/-- With the recognizers' decisions. -/
def upToRecognizer : List Internal.Decl := upToWalk ++ recognizer

/-- The development of the certificate {lit}`datatype-recognizer-fold`. -/
def recognizerFold : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-recognizer-fold.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom recognizerFoldChecked :
    checkedAfterIn extended3 (·.1.G) upToRecognizer recognizerFold = true

/-- With the recognizers' folds. -/
def upToRecognizerFold : List Internal.Decl := upToRecognizer ++ recognizerFold

/-- The development of the certificate {lit}`datatype-constructor`. -/
def ctor : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-constructor.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom ctorChecked :
    checkedAfterIn extended3 (·.1.G) upToRecognizerFold ctor = true

/-- With the constructors' fields. -/
def upToCtor : List Internal.Decl := upToRecognizerFold ++ ctor

/-- The development of the certificate {lit}`datatype-constructor-body`. -/
def ctorBody : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-constructor-body.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom ctorBodyChecked :
    checkedAfterIn extended3 (·.1.G) upToCtor ctorBody = true

/-- With the constructors' bodies. -/
def upToCtorBody : List Internal.Decl := upToCtor ++ ctorBody

/-- The development of the certificate {lit}`datatype-constructor-lam`. -/
def ctorLam : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-constructor-lam.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom ctorLamChecked :
    checkedAfterIn extended3 (·.1.G) upToCtorBody ctorLam = true

/-- With the abstractions of the constructors. -/
def upToCtorLam : List Internal.Decl := upToCtorBody ++ ctorLam

/-- The development of the certificate {lit}`datatype-constructor-nest`. -/
def ctorNest : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-constructor-nest.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom ctorNestChecked :
    checkedAfterIn extended3 (·.1.G) upToCtorLam ctorNest = true

/-- With the constructors' definitions. -/
def upToCtorNest : List Internal.Decl := upToCtorLam ++ ctorNest

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)
  (m : ProgramModel.{v} PST.1.G)

include h

/-- The theorems of {lit}`datatype-den` are valid in every model of the program. -/
theorem den_valid : m.Valid den :=
  DatatypeList.valid_after h (DatatypeCase.upToCase_valid h m) denChecked

/-- The theorems of {name}`upToWalkBase` are valid in every model of the program. -/
theorem upToWalkBase_valid : m.Valid upToWalkBase :=
  (DatatypeCase.upToCaseSound_valid h m).append (den_valid h m)

/-- The theorems of {lit}`datatype-walk` are valid in every model of the program. -/
theorem walk_valid : m.Valid walk :=
  DatatypeList.valid_after h (upToWalkBase_valid h m) walkChecked

/-- The theorems of {name}`upToWalk` are valid in every model of the program. -/
theorem upToWalk_valid : m.Valid upToWalk :=
  (upToWalkBase_valid h m).append (walk_valid h m)

/-- The theorems of {lit}`datatype-recognizer` are valid in every model of the program. -/
theorem recognizer_valid : m.Valid recognizer :=
  DatatypeList.valid_after h (upToWalk_valid h m) recognizerChecked

/-- The theorems of {name}`upToRecognizer` are valid in every model of the program. -/
theorem upToRecognizer_valid : m.Valid upToRecognizer :=
  (upToWalk_valid h m).append (recognizer_valid h m)

/-- The theorems of {lit}`datatype-recognizer-fold` are valid in every model of the program. -/
theorem recognizerFold_valid : m.Valid recognizerFold :=
  DatatypeList.valid_after h (upToRecognizer_valid h m) recognizerFoldChecked

/-- The theorems of {name}`upToRecognizerFold` are valid in every model of the program. -/
theorem upToRecognizerFold_valid : m.Valid upToRecognizerFold :=
  (upToRecognizer_valid h m).append (recognizerFold_valid h m)

/-- The theorems of {lit}`datatype-constructor` are valid in every model of the program. -/
theorem ctor_valid : m.Valid ctor :=
  DatatypeList.valid_after h (upToRecognizerFold_valid h m) ctorChecked

/-- The theorems of {name}`upToCtor` are valid in every model of the program. -/
theorem upToCtor_valid : m.Valid upToCtor :=
  (upToRecognizerFold_valid h m).append (ctor_valid h m)

/-- The theorems of {lit}`datatype-constructor-body` are valid in every model of the program. -/
theorem ctorBody_valid : m.Valid ctorBody :=
  DatatypeList.valid_after h (upToCtor_valid h m) ctorBodyChecked

/-- The theorems of {name}`upToCtorBody` are valid in every model of the program. -/
theorem upToCtorBody_valid : m.Valid upToCtorBody :=
  (upToCtor_valid h m).append (ctorBody_valid h m)

/-- The theorems of {lit}`datatype-constructor-lam` are valid in every model of the program. -/
theorem ctorLam_valid : m.Valid ctorLam :=
  DatatypeList.valid_after h (upToCtorBody_valid h m) ctorLamChecked

/-- The theorems of {name}`upToCtorLam` are valid in every model of the program. -/
theorem upToCtorLam_valid : m.Valid upToCtorLam :=
  (upToCtorBody_valid h m).append (ctorLam_valid h m)

/-- The theorems of {lit}`datatype-constructor-nest` are valid in every model of the program. -/
theorem ctorNest_valid : m.Valid ctorNest :=
  DatatypeList.valid_after h (upToCtorLam_valid h m) ctorNestChecked

/-- The theorems of {name}`upToCtorNest` are valid in every model of the program. -/
theorem upToCtorNest_valid : m.Valid upToCtorNest :=
  (upToCtorLam_valid h m).append (ctorNest_valid h m)

end GebTests.Prototypes.FreeTopos.Certified.DatatypeGenerated

end
