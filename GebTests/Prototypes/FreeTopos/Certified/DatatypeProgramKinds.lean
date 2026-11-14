/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgram
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgram -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The steps of a whole program's soundness at definitions, proved in the internal language

The developments of the invariant of a whole program's soundness and of its steps at the forms
that write a definition, a type or a numeral abbreviation, and at a template's instance, each
checked after the theorems of those before it, in the order of their search
({lit}`GebTests.Prototypes.FreeTopos.Certificates`).

## Main definitions

* {lit}`kinds`, {lit}`upToKinds` — the developments, and all with them.

## Main statements

* {lit}`upToKinds_valid` — their theorems are valid in every model of the program.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramKinds

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

/-- The developments of the invariant's parts and of the steps at the forms that write definitions,
in the order of their search. -/
def kinds : List (List Internal.Decl) :=
  [ofText (include_str "../../../../bootstrap/certificates/datatype-program-empty.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-forms.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-recs.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-occurs.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-nums.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-alias.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-alias-snoc.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-alias-ext.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-markers.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-top.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-nums-inv.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-let.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-defined.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-def.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-deftype.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-defnum.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-defn.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-generic.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-data.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-ctor.cert")]

set_option doc.verso false in
/-- Each of the developments checks in the extended program, after the theorems of those it
continues from and of those before it, as Lean's evaluator decides. -/
evaluation_axiom kindsChecked :
    checkedChainIn extended3 (·.1.G) kinds DatatypeProgram.upToRuns = true

/-- With the steps at the forms that write definitions. -/
def upToKinds : List Internal.Decl := DatatypeProgram.upToRuns ++ kinds.flatten

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)
  (m : ProgramModel.{v} PST.1.G)

include h

/-- The theorems of {name}`upToKinds` are valid in every model of the program. -/
theorem upToKinds_valid : m.Valid upToKinds :=
  ProgramModel.Valid.chain h kinds (DatatypeProgram.upToRuns_valid h m) kindsChecked

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramKinds

end
