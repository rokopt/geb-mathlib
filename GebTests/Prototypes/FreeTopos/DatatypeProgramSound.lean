/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeClosed
public import GebTests.Prototypes.FreeTopos.DatatypeProgramData
public meta import GebTests.Prototypes.FreeTopos.DatatypeClosed -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeProgramData -- shake: keep

set_option doc.verso true in
/-!
# The developments of a whole program's soundness

The developments of the soundness of a whole program of the datatype language
({lit}`programForms`), each with the name of its certificate, in the order in which each
continues from those before it, and their storing as certificates after the certificates they
continue from.

## Main definitions

* {lit}`programSoundGroups` — the developments, each with its certificate's name.
* {lit}`programSoundBefore` — the certificates the developments continue from.
* {lit}`programSoundCertificates` — the developments, each stored as its certificate.

## Tags

internal language, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- The developments of the soundness of a whole program, each with its certificate's name, in
the order in which each continues from those before it: the runs' ({name}`stepGroups`); the
invariant's parts at the states the passes begin in and under the passes' steps; the steps at
the forms that write a definition, a type or a numeral abbreviation, and at a template's
instance; the soundness of a constructor's definition at the passes' states; the steps at a
datatype's node, at its marker and at its constructors' definitions, and the step at a
datatype's declaration; then the kinds of forms, the induction on the forms and the program's
soundness, with hypotheses and as one formula without them. -/
def programSoundGroups (P : Prog) (S : Defs) (T : Defs3) : List (String × List Step) :=
  stepGroups P S T ++
    [("datatype-program-empty", programEmptyDev P S T),
      ("datatype-program-forms", [eraseDefForm P S, recAtThree P S, eraseOther P S]),
      ("datatype-program-recs", programRecsDev P S T),
      ("datatype-program-occurs", programOccursDev P S),
      ("datatype-program-nums", programNumsDev P S),
      ("datatype-program-alias",
        foldRebuild P "rt" "Typing.readTy" [treeTy, T.envTy] ++
        [foldKids P S "rt" "Typing.readTy" [treeTy, T.envTy]] ++
        foldRebuild (aliasProg P) "ea" "Datatype.expandAliases" [treeTy, list treeTy] ++
        [foldKids (aliasProg P) S "ea" "Datatype.expandAliases" [treeTy, list treeTy],
          rawAtomEq P S T, cohAt P S T, cohRead P S T]),
      ("datatype-program-alias-snoc", [findAliasSnoc P S, aliasTysExtend P S]),
      ("datatype-program-alias-ext", [kwReserved P S "kwTReserved" "Reader.kwT",
        kwReserved P S "kwUnitReserved" "Reader.kwUnit", aliasExtend P S T]),
      ("datatype-program-markers", [markersKernel P S]),
      ("datatype-program-top", programTopDev P S T),
      ("datatype-program-nums-inv", programNumsInvDev P S T),
      ("datatype-program-let", programLetDev P S T),
      ("datatype-program-defined", [writtenInv P S T, stepDefined P S T]),
      ("datatype-program-def", [stepDef P S T]),
      ("datatype-program-deftype", [stepDeftype P S T]),
      ("datatype-program-defnum", [numOfParts P S, stepDefnum P S T]),
      ("datatype-program-defn", [stepDefn P S T]),
      ("datatype-program-generic", [xpGeneric P S, checkGeneric P S T, stepGeneric P S T]),
      ("datatype-program-data", programDataDev P S T),
      ("datatype-program-ctor", [ctorDeclPlain P S, soundOfFormAll P S T]),
      ("datatype-program-user", [implAbsent P S, globAbsent P S T]),
      ("datatype-program-num", [numOfKws P S T]),
      ("datatype-program-field", [fieldAllOf P S T]),
      ("datatype-program-coh", [quoteInj P S, relDataElim P S T, cohOfRead P S T,
        fieldsTypedRead P S T]),
      ("datatype-program-coh-fields", [cohFields P S T]),
      ("datatype-program-read-some", [lookupAbbrevSome P S, readTypeSome P S]),
      ("datatype-program-lam-resolved", [lamBindersRead P S T, binderTypeRead P S T]),
      ("datatype-program-read-fields", [fieldsResolvedRead P S T]),
      ("datatype-program-ctor-atoms", (ctorAtoms P).zipIdx.map (fun (n, i) ↦
        atomExcluded P S s!"ctorExcluded{i}" n) ++ [nodePrimitive P S]),
      ("datatype-program-ctor-sound", [ctorSoundAt P S T]),
      ("datatype-program-data-inv", [eraseData P S, aliasTysWeaken P S, dataInv P S T]),
      ("datatype-program-marker-skip", [eraseMarker P S, recAtMarker P S, allIndexed P S,
        markerSkipped P S T]),
      ("datatype-program-writer-atoms", writerAtomsDev P S),
      ("datatype-program-recognizer-at", [ctorsIndexed P S, recognizerAt P S T]),
      ("datatype-program-marker-read", [globSnoc P S T, markerReadAt P S T]),
      ("datatype-program-decls", [dataDeclAt P S, declsNoAlias P S, findAliasAppend P S]),
      ("datatype-program-block-facts", [aliasSame P S T false, aliasSame P S T true,
        dataRead P S T, kernelAfter P S]),
      ("datatype-program-entries", [anyAt P S, ctorEntry P S]),
      ("datatype-program-block-end", [blockEndAt P S T, blockEnd P S T]),
      ("datatype-program-var-eqs", [nestAppend P S, ctorDeclVar P S, ctorEntryVar P S]),
      ("datatype-program-var-read", [rawPairEq P S T, readTyList P S T]),
      ("datatype-program-var-rest", [atomExcluded P S "restExcluded"
        (atomNameT (pc P "Datatype.aRest" [])), restBinderRead P S T]),
      ("datatype-program-var-sound", [ctorSoundVarAt P S T]),
      ("datatype-program-block-ctor", [blockCtor P S T false, blockCtor P S T true]),
      ("datatype-program-ctors", [ctorFlag P S, ctorsInv P S T]),
      ("datatype-program-data-step", [stepData P S T]),
      ("datatype-program-defs", neqMore P ++ [formKind P S, passesForms P S T]),
      ("datatype-program-sound", [programForms P S T]),
      ("datatype-program-closed", [programClosed P S T])]

/-- The names of the certificates the developments of the soundness of a whole program continue
from, in order: those the soundness of the definitions the expansion generates continues from
and its own, to the constructors' abstractions; then the typing's runs', the soundness at every
tree's, and those of the stage functions at applications and of abstractions over lists of
binders. -/
def programSoundBefore : List String :=
  ["datatype-base", "datatype-atom", "datatype-list", "datatype-stages", "datatype-apply",
    "datatype-expansion", "datatype-assembly", "datatype-datum", "datatype-decode",
    "datatype-folds", "datatype-case", "datatype-clauses", "datatype-case-sound", "datatype-den",
    "datatype-walk", "datatype-recognizer", "datatype-recognizer-fold", "datatype-constructor",
    "datatype-constructor-body", "datatype-constructor-lam", "datatype-constructor-nest",
    "datatype-program", "datatype-closed", "datatype-app", "datatype-lam"]

/-- The names of the lemmas of the certificates of {name}`programSoundBefore`, in order. A name
that more than one of them states is cited as the first states it. -/
def programSoundNames (P : Prog) (S : Defs) (T : Defs3) : Option (List String) := do
  let generated ← walkAfter P S T
  pure (generated ++ (walkDev P S T ++ recognizerDev P S T ++ recognizerFoldDev P S T ++
    constructorDev P S T ++ constructorBodyDev P S T ++ constructorLamDev P S T ++
    constructorNestDev P S T ++ programDev P S T ++ closedDev P S T ++ appDev3 P S T ++
    lamDev3 P S T).map (·.1))

/-- The developments of the soundness of a whole program ({name}`programSoundGroups`), each
stored as its certificate, after the theorems of the certificates of
{name}`programSoundBefore` and of the developments before it. -/
def programSoundCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := programSoundNames P S T | throw "the base is not stated"
  let thmsOf (c : Stored.Cert) : Except String (List Internal.Thm) :=
    match Stored.declsOfNats c.table with
    | some ds => pure (ds.filterMap fun
      | .language a _ => some a
      | _ => none)
    | none => throw s!"{c.name} does not read back"
  let (_, _, certs) ← (programSoundGroups P S T).foldlM
    (fun (names, before, certs) (cert, steps) ↦ do
      let cs ← certifyAfter P names cert steps before
      let thms ← cs.mapM thmsOf
      pure (names ++ steps.map (·.1), before ++ thms.flatten, certs ++ cs))
    (names, before, ([] : List Stored.Cert))
  pure certs

end GebTests.Prototypes.FreeTopos.Datatypes

end
