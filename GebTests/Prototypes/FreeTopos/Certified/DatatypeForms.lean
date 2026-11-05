/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeList
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeList -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness given the later keywords', proved in the internal language

The developments of the applications, the abstractions, the representations, the kernel's constants
and every list, stored in the certificates of {lit}`bootstrap/certificates/` that continue from the
keywords' forms' ({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeList`). Each is checked
after the statements of the theorems it continues from, and its theorems are valid in every model of
the program in which those are, so that a check reads no derivation of another development.

## Main statements

* {lit}`sound_valid` — the soundness at every tree, given the later keywords', is valid in every
  model of the program.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeForms

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

/-- The development of the certificate {lit}`datatype-stages`. -/
def stages : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-stages.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom stagesChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeList.decls stages = true

/-- The base, atoms and keywords' forms and the stage functions. -/
def upToStages : List Internal.Decl := DatatypeList.decls ++ stages

/-- The development of the certificate {lit}`datatype-apply`. -/
def apply : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-apply.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom applyChecked :
    checkedAfterIn extended3 (·.1.G) upToStages apply = true

/-- With the applications at expanded forms. -/
def upToApply : List Internal.Decl := upToStages ++ apply

/-- The development of the certificate {lit}`datatype-expansion`. -/
def expansion : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-expansion.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom expansionChecked :
    checkedAfterIn extended3 (·.1.G) upToApply expansion = true

/-- With the expansion of lists. -/
def upToExpansion : List Internal.Decl := upToApply ++ expansion

/-- The development of the certificate {lit}`datatype-assembly`. -/
def assembly : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-assembly.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom assemblyChecked :
    checkedAfterIn extended3 (·.1.G) upToExpansion assembly = true

/-- With the keywords' arities and the atoms' applications. -/
def upToAssembly : List Internal.Decl := upToExpansion ++ assembly

/-- The development of the certificate {lit}`datatype-app`. -/
def app : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-app.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom appChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeList.decls app = true

/-- The development of the certificate {lit}`datatype-lam`. -/
def lam : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-lam.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom lamChecked :
    checkedAfterIn extended3 (·.1.G) (DatatypeList.decls ++ app ++ stages) lam = true

/-- The development of the certificate {lit}`datatype-data`. -/
def data : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-data.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom dataChecked :
    checkedAfterIn extended3 (·.1.G) upToAssembly data = true

/-- The development of the certificate {lit}`datatype-folds`. -/
def folds : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-folds.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom foldsChecked :
    checkedAfterIn extended3 (·.1.G) upToAssembly folds = true

/-- With the applications, the abstractions, the representations and the constants. -/
def upToFolds : List Internal.Decl := upToAssembly ++ app ++ lam ++ data ++ folds

/-- The development of the certificate {lit}`datatype-lists`. -/
def lists : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-lists.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom listsChecked :
    checkedAfterIn extended3 (·.1.G) upToFolds lists = true

/-- The development of the certificate {lit}`datatype-sound`. -/
def sound : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-sound.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom soundChecked :
    checkedAfterIn extended3 (·.1.G) (upToFolds ++ lists) sound = true

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)
  (m : ProgramModel.{v} PST.1.G)

include h

/-- The theorems of {lit}`datatype-stages` are valid in every model of the program. -/
theorem stages_valid : m.Valid stages :=
  DatatypeList.valid_after h (DatatypeList.decls_valid h m) stagesChecked

/-- The theorems of {name}`upToStages` are valid in every model of the program. -/
theorem upToStages_valid : m.Valid upToStages :=
  (DatatypeList.decls_valid h m).append (stages_valid h m)

/-- The theorems of {lit}`datatype-apply` are valid in every model of the program. -/
theorem apply_valid : m.Valid apply :=
  DatatypeList.valid_after h (upToStages_valid h m) applyChecked

/-- The theorems of {name}`upToApply` are valid in every model of the program. -/
theorem upToApply_valid : m.Valid upToApply :=
  (upToStages_valid h m).append (apply_valid h m)

/-- The theorems of {lit}`datatype-expansion` are valid in every model of the program. -/
theorem expansion_valid : m.Valid expansion :=
  DatatypeList.valid_after h (upToApply_valid h m) expansionChecked

/-- The theorems of {name}`upToExpansion` are valid in every model of the program. -/
theorem upToExpansion_valid : m.Valid upToExpansion :=
  (upToApply_valid h m).append (expansion_valid h m)

/-- The theorems of {lit}`datatype-assembly` are valid in every model of the program. -/
theorem assembly_valid : m.Valid assembly :=
  DatatypeList.valid_after h (upToExpansion_valid h m) assemblyChecked

/-- The theorems of {name}`upToAssembly` are valid in every model of the program. -/
theorem upToAssembly_valid : m.Valid upToAssembly :=
  (upToExpansion_valid h m).append (assembly_valid h m)

/-- The theorems of {lit}`datatype-app` are valid in every model of the program. -/
theorem app_valid : m.Valid app :=
  DatatypeList.valid_after h (DatatypeList.decls_valid h m) appChecked

/-- The theorems of {lit}`datatype-lam` are valid in every model of the program. -/
theorem lam_valid : m.Valid lam :=
  DatatypeList.valid_after h (((DatatypeList.decls_valid h m).append (app_valid h m)).append
    (stages_valid h m)) lamChecked

/-- The theorems of {lit}`datatype-data` are valid in every model of the program. -/
theorem data_valid : m.Valid data :=
  DatatypeList.valid_after h (upToAssembly_valid h m) dataChecked

/-- The theorems of {lit}`datatype-folds` are valid in every model of the program. -/
theorem folds_valid : m.Valid folds :=
  DatatypeList.valid_after h (upToAssembly_valid h m) foldsChecked

/-- The theorems of {name}`upToFolds` are valid in every model of the program. -/
theorem upToFolds_valid : m.Valid upToFolds :=
  ((((upToAssembly_valid h m).append (app_valid h m)).append (lam_valid h m)).append (data_valid h
    m)).append (folds_valid h m)

/-- The theorems of {lit}`datatype-lists` are valid in every model of the program. -/
theorem lists_valid : m.Valid lists :=
  DatatypeList.valid_after h (upToFolds_valid h m) listsChecked

/-- The theorems of {lit}`datatype-sound` are valid in every model of the program. -/
theorem sound_valid : m.Valid sound :=
  DatatypeList.valid_after h ((upToFolds_valid h m).append (lists_valid h m)) soundChecked

end GebTests.Prototypes.FreeTopos.Certified.DatatypeForms

end
