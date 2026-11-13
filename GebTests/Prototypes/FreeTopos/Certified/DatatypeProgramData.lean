/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramKinds
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramKinds -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The step of a whole program's soundness at a datatype, proved in the internal language

The developments of the soundness of a constructor's definition at the passes' states and of
the step of a whole program's soundness at a datatype's declaration, each checked after the
theorems of those before it, in the order of their search
({lit}`GebTests.Prototypes.FreeTopos.Certificates`).

## Main definitions

* {lit}`data`, {lit}`upToData` — the developments, and all with them.

## Main statements

* {lit}`upToData_valid` — their theorems are valid in every model of the program.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramData

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

/-- The developments of the constructors' soundness at the passes' states and of the step at a
datatype's declaration, in the order of their search. -/
def data : List (List Internal.Decl) :=
  [ofText (include_str "../../../../bootstrap/certificates/datatype-program-user.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-num.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-field.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-coh.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-coh-fields.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-read-some.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-lam-resolved.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-read-fields.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-ctor-atoms.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-ctor-sound.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-data-inv.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-marker-skip.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-writer-atoms.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-recognizer-at.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-marker-read.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-decls.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-block-facts.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-entries.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-block-end.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-var-eqs.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-var-read.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-var-rest.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-var-sound.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-block-ctor.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-ctors.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-data-step.cert")]

set_option doc.verso false in
/-- Each of the developments checks in the extended program, after the theorems of those it
continues from and of those before it, as Lean's evaluator decides. -/
evaluation_axiom dataChecked :
    checkedChainIn extended3 (·.1.G) data DatatypeProgramKinds.upToKinds = true

/-- With the step at a datatype's declaration. -/
def upToData : List Internal.Decl := DatatypeProgramKinds.upToKinds ++ data.flatten

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)
  (m : ProgramModel.{v} PST.1.G)

include h

/-- The theorems of {name}`upToData` are valid in every model of the program. -/
theorem upToData_valid : m.Valid upToData :=
  ProgramModel.Valid.chain h data (DatatypeProgramKinds.upToKinds_valid h m) dataChecked

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramData

end
