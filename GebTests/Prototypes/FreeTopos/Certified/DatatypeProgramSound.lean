/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramData
public import GebTests.Prototypes.FreeTopos.DatatypeProgramStep
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramData -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeProgramStep -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a whole program, proved in the internal language

The soundness of a whole program of the datatype language's stage-1 compiler: the developments
of the kinds of forms, of the induction on a program's forms and of the program's soundness,
each checked after the theorems of those before it, in the order of their search
({lit}`GebTests.Prototypes.FreeTopos.Certificates`).

## Main statements

* {lit}`programForms_valid` — the soundness of a whole program is valid in every model of the
  program.
* {lit}`programClosed_valid` — so is the soundness as one formula without hypotheses.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramSound

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

/-- The developments of the kinds of forms and of the induction on a program's forms. -/
def defs : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-program-defs.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as
Lean's evaluator decides. -/
evaluation_axiom defsChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeProgramData.upToData defs = true

/-- With the induction on a program's forms. -/
def upToDefs : List Internal.Decl := DatatypeProgramData.upToData ++ defs

/-- The development of the certificate {lit}`datatype-program-sound`. -/
def sound : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-program-sound.cert")

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

/-- With the program's soundness. -/
def upToSound : List Internal.Decl := upToDefs ++ sound

/-- The development of the certificate {lit}`datatype-program-closed`. -/
def closed : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-program-closed.cert")

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

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)
  (m : ProgramModel.{v} PST.1.G)

include h

/-- The theorems of {lit}`datatype-program-defs` are valid in every model of the program. -/
theorem defs_valid : m.Valid defs :=
  DatatypeList.valid_after h (DatatypeProgramData.upToData_valid h m) defsChecked

/-- The theorems of {name}`upToDefs` are valid in every model of the program. -/
theorem upToDefs_valid : m.Valid upToDefs :=
  (DatatypeProgramData.upToData_valid h m).append (defs_valid h m)

/-- The theorems of {lit}`datatype-program-sound` are valid in every model of the program. -/
theorem sound_valid : m.Valid sound :=
  DatatypeList.valid_after h (upToDefs_valid h m) soundChecked

/-- The soundness of a whole program of the datatype language's stage-1 compiler
({name}`programFormsThm`) is valid in every model of the program. -/
theorem programForms_valid {a : Internal.Thm}
    (ha : programFormsThm PST.1 PST.2.1 PST.2.2 = some a) : a.Valid m.M PST.1.G := by
  have hl := mem_thmsOf_of_statesLastIn h soundStates
  have hs : soundThm PST = a := by simp [soundThm, ha]
  exact hs ▸ sound_valid h m _ hl

/-- The theorems of {name}`upToSound` are valid in every model of the program. -/
theorem upToSound_valid : m.Valid upToSound :=
  (upToDefs_valid h m).append (sound_valid h m)

/-- The theorems of {lit}`datatype-program-closed` are valid in every model of the program. -/
theorem closed_valid : m.Valid closed :=
  DatatypeList.valid_after h (upToSound_valid h m) closedChecked

/-- The soundness of a whole program as one formula without hypotheses
({name}`programClosedThm`) is valid in every model of the program. -/
theorem programClosed_valid {a : Internal.Thm}
    (ha : programClosedThm PST.1 PST.2.1 PST.2.2 = some a) : a.Valid m.M PST.1.G := by
  have hl := mem_thmsOf_of_statesLastIn h closedStates
  have hs : closedThm PST = a := by simp [closedThm, ha]
  exact hs ▸ closed_valid h m _ hl

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramSound

end
