/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeDatum
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeDatum -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at case analysis, proved in the internal language

The developments of the soundness at a case analysis: the walk of a clause's fields, the chain of
its clauses and the source form, each checked after the statements of the theorems it continues from
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeDatum`).

## Main statements

* {lit}`caseSound_valid` — their theorems are valid in every model of the program.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeCase

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

/-- The developments the case analyses continue from. -/
def upToFolds : List Internal.Decl :=
  DatatypeForms.upToAssembly ++ DatatypeDatum.datum ++ DatatypeDatum.decode ++
    DatatypeForms.folds

/-- The development of the certificate {lit}`datatype-case`. -/
def caseDev : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-case.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom caseDevChecked :
    checkedAfterIn extended3 (·.1.G) upToFolds caseDev = true

/-- With the walk of a clause's fields. -/
def upToCase : List Internal.Decl := upToFolds ++ caseDev

/-- The development of the certificate {lit}`datatype-clauses`. -/
def clauses : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-clauses.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom clausesChecked :
    checkedAfterIn extended3 (·.1.G) upToCase clauses = true

/-- With the chain of the clauses. -/
def upToClauses : List Internal.Decl := upToCase ++ clauses

/-- The development of the certificate {lit}`datatype-case-sound`. -/
def caseSound : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-case-sound.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom caseSoundChecked :
    checkedAfterIn extended3 (·.1.G) upToClauses caseSound = true

/-- With the soundness at a case analysis. -/
def upToCaseSound : List Internal.Decl := upToClauses ++ caseSound

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)
  (m : ProgramModel.{v} PST.1.G)

include h

/-- The theorems of {name}`upToFolds` are valid in every model of the program. -/
theorem upToFolds_valid : m.Valid upToFolds :=
  (((DatatypeForms.upToAssembly_valid h m).append (DatatypeDatum.datum_valid h m)).append
    (DatatypeDatum.decode_valid h m)).append (DatatypeForms.folds_valid h m)

/-- The theorems of {lit}`datatype-case` are valid in every model of the program. -/
theorem caseDev_valid : m.Valid caseDev :=
  DatatypeList.valid_after h (upToFolds_valid h m) caseDevChecked

/-- The theorems of {name}`upToCase` are valid in every model of the program. -/
theorem upToCase_valid : m.Valid upToCase :=
  (upToFolds_valid h m).append (caseDev_valid h m)

/-- The theorems of {lit}`datatype-clauses` are valid in every model of the program. -/
theorem clauses_valid : m.Valid clauses :=
  DatatypeList.valid_after h (upToCase_valid h m) clausesChecked

/-- The theorems of {name}`upToClauses` are valid in every model of the program. -/
theorem upToClauses_valid : m.Valid upToClauses :=
  (upToCase_valid h m).append (clauses_valid h m)

/-- The theorems of {lit}`datatype-case-sound` are valid in every model of the program. -/
theorem caseSound_valid : m.Valid caseSound :=
  DatatypeList.valid_after h (upToClauses_valid h m) caseSoundChecked

/-- The theorems of {name}`upToCaseSound` are valid in every model of the program. -/
theorem upToCaseSound_valid : m.Valid upToCaseSound :=
  (upToClauses_valid h m).append (caseSound_valid h m)

end GebTests.Prototypes.FreeTopos.Certified.DatatypeCase

end
