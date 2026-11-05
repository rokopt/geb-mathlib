/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeForms
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeForms -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at datums and decodings, proved in the internal language

The developments of the soundness at a datum and at a decoding of their numbers of elements, each
checked after the statements of the theorems it continues from
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeForms`).

## Main statements

* {lit}`datumCase_valid`, {lit}`decodeCase_valid` — their theorems are valid in every model of the
  program.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeDatum

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

/-- The development of the certificate {lit}`datatype-datum`. -/
def datum : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-datum.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom datumChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeList.decls datum = true

/-- The development of the certificate {lit}`datum-case`. -/
def datumCase : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datum-case.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom datumCaseChecked :
    checkedAfterIn extended3 (·.1.G) (DatatypeList.decls ++ datum) datumCase = true

/-- The development of the certificate {lit}`datatype-decode`. -/
def decode : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-decode.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom decodeChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeForms.upToAssembly decode = true

/-- The development of the certificate {lit}`decode-case`. -/
def decodeCase : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/decode-case.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom decodeCaseChecked :
    checkedAfterIn extended3 (·.1.G) (DatatypeForms.upToAssembly ++ datum ++ decode) decodeCase =
      true

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)
  (m : ProgramModel.{v} PST.1.G)

include h

/-- The theorems of {lit}`datatype-datum` are valid in every model of the program. -/
theorem datum_valid : m.Valid datum :=
  DatatypeList.valid_after h (DatatypeList.decls_valid h m) datumChecked

/-- The theorems of {lit}`datum-case` are valid in every model of the program. -/
theorem datumCase_valid : m.Valid datumCase :=
  DatatypeList.valid_after h ((DatatypeList.decls_valid h m).append (datum_valid h m))
    datumCaseChecked

/-- The theorems of {lit}`datatype-decode` are valid in every model of the program. -/
theorem decode_valid : m.Valid decode :=
  DatatypeList.valid_after h (DatatypeForms.upToAssembly_valid h m) decodeChecked

/-- The theorems of {lit}`decode-case` are valid in every model of the program. -/
theorem decodeCase_valid : m.Valid decodeCase :=
  DatatypeList.valid_after h (((DatatypeForms.upToAssembly_valid h m).append (datum_valid h
    m)).append (decode_valid h m)) decodeCaseChecked

end GebTests.Prototypes.FreeTopos.Certified.DatatypeDatum

end
