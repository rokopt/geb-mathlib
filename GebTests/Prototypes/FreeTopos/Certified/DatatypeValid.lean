/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCase
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCata
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCataChain
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCataClauses
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCataCore
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCataSound
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCataSrc
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeClosed
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeDatum
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeForms
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeGenerated
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeList
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgram
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramData
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramKinds
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramSound
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The developments of the datatype language's soundness are valid

The theorems of the developments of the datatype language's soundness are valid in every model of
the program the soundness is stated in. A development checks after the statements of the theorems it
continues from, as the modules of its group state by evaluation, each importing the developments'
declarations and no other check; its theorems are therefore valid in a model in which those are
({name}`GebTests.Prototypes.FreeTopos.Certified.DatatypeList.valid_after`), and this module composes
the checks in the order of the developments, from the validity of the first group's
({name}`GebTests.Prototypes.FreeTopos.Certified.DatatypeList.decls_valid`).

## Main statements

* {lit}`DatatypeForms.sound_valid` — the soundness at every tree, given the later keywords', is
  valid in every model of the program.
* {lit}`DatatypeDatum.datumCase_valid`, {lit}`DatatypeDatum.decodeCase_valid` — the developments'
  theorems are valid in every model of the program.
* {lit}`DatatypeCase.caseSound_valid` — the developments' theorems are valid in every model of the
  program.
* {lit}`DatatypeCata.cataSrc_valid` — the developments' theorems are valid in every model of the
  program.
* {lit}`DatatypeGenerated.upToCtorNest_valid` — the theorems of the developments are valid in every
  model of the program.
* {lit}`DatatypeClosed.sound_valid` — the soundness at every tree is valid in every model of the
  program.
* {lit}`DatatypeProgram.upToRuns_valid` — the developments' theorems are valid in every model of the
  program.
* {lit}`DatatypeProgramKinds.upToKinds_valid` — the developments' theorems are valid in every model
  of the program.
* {lit}`DatatypeProgramData.upToData_valid` — the developments' theorems are valid in every model of
  the program.
* {lit}`DatatypeProgramSound.programForms_valid` — the soundness of a whole program is valid in
  every model of the program.
* {lit}`DatatypeProgramSound.programClosed_valid` — so is the soundness as one formula without
  hypotheses.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)
  (m : ProgramModel.{v} PST.1.G)

include h

namespace DatatypeForms

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

end DatatypeForms

namespace DatatypeDatum

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

end DatatypeDatum

namespace DatatypeCase

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

end DatatypeCase

namespace DatatypeCata

/-- The theorems of {lit}`datatype-cata` are valid in every model of the program. -/
theorem cata_valid : m.Valid cata :=
  DatatypeList.valid_after h (DatatypeCase.upToCaseSound_valid h m) cataChecked

/-- The theorems of {name}`upToCata` are valid in every model of the program. -/
theorem upToCata_valid : m.Valid upToCata :=
  (DatatypeCase.upToCaseSound_valid h m).append (cata_valid h m)

/-- The theorems of {lit}`datatype-cata-clauses` are valid in every model of the program. -/
theorem cataClauses_valid : m.Valid cataClauses :=
  DatatypeList.valid_after h (upToCata_valid h m) cataClausesChecked

/-- The theorems of {name}`upToCataClauses` are valid in every model of the program. -/
theorem upToCataClauses_valid : m.Valid upToCataClauses :=
  (upToCata_valid h m).append (cataClauses_valid h m)

/-- The theorems of {lit}`datatype-cata-chain` are valid in every model of the program. -/
theorem cataChain_valid : m.Valid cataChain :=
  DatatypeList.valid_after h (upToCataClauses_valid h m) cataChainChecked

/-- The theorems of {name}`upToCataChain` are valid in every model of the program. -/
theorem upToCataChain_valid : m.Valid upToCataChain :=
  (upToCataClauses_valid h m).append (cataChain_valid h m)

/-- The theorems of {lit}`datatype-cata-sound` are valid in every model of the program. -/
theorem cataSound_valid : m.Valid cataSound :=
  DatatypeList.valid_after h (upToCataChain_valid h m) cataSoundChecked

/-- The theorems of {name}`upToCataSound` are valid in every model of the program. -/
theorem upToCataSound_valid : m.Valid upToCataSound :=
  (upToCataChain_valid h m).append (cataSound_valid h m)

/-- The theorems of {lit}`datatype-cata-core` are valid in every model of the program. -/
theorem cataCore_valid : m.Valid cataCore :=
  DatatypeList.valid_after h (upToCataSound_valid h m) cataCoreChecked

/-- The theorems of {name}`upToCataCore` are valid in every model of the program. -/
theorem upToCataCore_valid : m.Valid upToCataCore :=
  (upToCataSound_valid h m).append (cataCore_valid h m)

/-- The theorems of {lit}`datatype-cata-src` are valid in every model of the program. -/
theorem cataSrc_valid : m.Valid cataSrc :=
  DatatypeList.valid_after h (upToCataCore_valid h m) cataSrcChecked

/-- The theorems of {name}`upToCataSrc` are valid in every model of the program. -/
theorem upToCataSrc_valid : m.Valid upToCataSrc :=
  (upToCataCore_valid h m).append (cataSrc_valid h m)

end DatatypeCata

namespace DatatypeGenerated

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

end DatatypeGenerated

namespace DatatypeClosed

/-- The theorems of {name}`before` are valid in every model of the program. -/
theorem before_valid : m.Valid before :=
  (((((((DatatypeCata.upToCataSrc_valid h m).append (DatatypeDatum.datumCase_valid h m)).append
    (DatatypeDatum.decodeCase_valid h m)).append (DatatypeForms.app_valid h m)).append
    (DatatypeForms.lam_valid h m)).append (DatatypeForms.data_valid h m)).append
    (DatatypeForms.lists_valid h m)).append (DatatypeForms.sound_valid h m)

/-- The theorems of {lit}`datatype-closed` are valid in every model of the program. -/
theorem closed_valid : m.Valid closed :=
  DatatypeList.valid_after h (before_valid h m) closedChecked

/-- The soundness of the datatype language's stage-1 compiler at every tree, without hypotheses
({name}`soundClosedThm`), is valid in every model of the program. -/
theorem sound_valid : (soundClosedThm PST.1 PST.2.1 PST.2.2).Valid m.M PST.1.G :=
  have hl := mem_thmsOf_of_statesLastIn h closedStates
  closed_valid h m _ hl

end DatatypeClosed

namespace DatatypeProgram

/-- The theorems of {lit}`datatype-base` are valid in every model of the program. -/
theorem base_valid : m.Valid base :=
  (DatatypeList.decls_valid h m).left.left

/-- The theorems of {lit}`datatype-program` are valid in every model of the program. -/
theorem program_valid : m.Valid program :=
  DatatypeList.valid_after h (base_valid h m) programChecked

/-- The theorems of {name}`before` are valid in every model of the program. -/
theorem before_valid : m.Valid before :=
  ((((DatatypeGenerated.upToCtorNest_valid h m).append (program_valid h m)).append
    (DatatypeClosed.closed_valid h m)).append (DatatypeForms.app_valid h m)).append
    (DatatypeForms.lam_valid h m)

/-- The theorems of {name}`upToRuns` are valid in every model of the program. -/
theorem upToRuns_valid : m.Valid upToRuns :=
  ProgramModel.Valid.chain h runs (before_valid h m) runsChecked

end DatatypeProgram

namespace DatatypeProgramKinds

/-- The theorems of {name}`upToKinds` are valid in every model of the program. -/
theorem upToKinds_valid : m.Valid upToKinds :=
  ProgramModel.Valid.chain h kinds (DatatypeProgram.upToRuns_valid h m) kindsChecked

end DatatypeProgramKinds

namespace DatatypeProgramData

/-- The theorems of {name}`upToData` are valid in every model of the program. -/
theorem upToData_valid : m.Valid upToData :=
  ProgramModel.Valid.chain h data (DatatypeProgramKinds.upToKinds_valid h m) dataChecked

end DatatypeProgramData

namespace DatatypeProgramSound

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

end DatatypeProgramSound

end GebTests.Prototypes.FreeTopos.Certified

end
