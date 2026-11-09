/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeApply
public import GebTests.Prototypes.FreeTopos.DatatypeCase
public import GebTests.Prototypes.FreeTopos.DatatypeClauses
public import GebTests.Prototypes.FreeTopos.DatatypeCata
public import GebTests.Prototypes.FreeTopos.DatatypeCataChain
public import GebTests.Prototypes.FreeTopos.DatatypeCataClauses
public import GebTests.Prototypes.FreeTopos.DatatypeCataSound
public import GebTests.Prototypes.FreeTopos.DatatypeCataSrc
public import GebTests.Prototypes.FreeTopos.DatatypeClosed
public import GebTests.Prototypes.FreeTopos.DatatypeLists
public import GebTests.Prototypes.FreeTopos.DatatypeData
public import GebTests.Prototypes.FreeTopos.DatatypeDatum
public import GebTests.Prototypes.FreeTopos.DatatypeDecode
public import GebTests.Prototypes.FreeTopos.DatatypeFolds
public import GebTests.Prototypes.FreeTopos.DatatypeSound
public import GebTests.Prototypes.FreeTopos.DatatypeLam
public import GebTests.Prototypes.FreeTopos.DatatypeConstructor
public import GebTests.Prototypes.FreeTopos.DatatypeProgram
public import GebTests.Prototypes.FreeTopos.Expansion
public import GebTests.Prototypes.FreeTopos.Normalization

set_option doc.verso true in
/-!
# The searches of the developments of the internal language

The developments the internal language proves about the programs of the bootstrap are found by
the proofs of their modules, which search for derivations, and are stored, each as the list of its
declarations, in a file of {lit}`bootstrap/certificates/`, which the modules stating the theorems
read and check. {lit}`GebTests.Prototypes.FreeTopos.StoredWriter` runs the searches and writes
the certificates, as {lit}`scripts/certificates.sh` runs it; the search is the costly part, and is
run when the proofs or the programs change, as the bootstrap's artifacts are regenerated. A
certificate is the table of the distinct nodes of the development's tree, read by
{lit}`GebTests.Prototypes.FreeTopos.Stored`.

## Main definitions

* {lit}`searches` — the searches that find the developments, each with its name.

## Tags

internal language, development, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certificates

open Geb Geb.FreeTopos

/-- A search of a translated program's developments: each development as a certificate, where the
program translates and every lemma is proved. -/
def inProgram {α : Type} (program : Option α)
    (search : α → Except String (List Stored.Cert)) :
    Except String (List Stored.Cert) :=
  match program with
  | some P => search P
  | none => .error "the program does not translate"

/-- A search of developments: the names of the certificates it continues from, and, given their
theorems in that order, each development as a certificate, or the reason a lemma is not proved. -/
abbrev Search :=
  List String × (List (List Internal.Thm) → Except String (List Stored.Cert))

set_option compiler.extract_closed false in
/-- The searches of the developments of the definitions the expansion generates, and of the
typing's runs over a program's forms. -/
def generatedSearches : List (String × Search) :=
  [("datatype-den", (["datatype-base", "datatype-atom", "datatype-list",
      "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
      "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case"], fun dss ↦
    inProgram Datatypes.extended3 fun (P, S, T) ↦
      Datatypes.denCertificates P S T dss.flatten)),
    ("datatype-walk", (["datatype-base", "datatype-atom", "datatype-list",
      "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
      "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case", "datatype-clauses",
      "datatype-case-sound", "datatype-den"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.walkCertificates P S T dss.flatten)),
    ("datatype-recognizer", (["datatype-base", "datatype-atom", "datatype-list",
      "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
      "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case", "datatype-clauses",
      "datatype-case-sound", "datatype-den", "datatype-walk"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.recognizerCertificates P S T dss.flatten)),
    ("datatype-recognizer-fold", (["datatype-base", "datatype-atom", "datatype-list",
      "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
      "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case", "datatype-clauses",
      "datatype-case-sound", "datatype-den", "datatype-walk", "datatype-recognizer"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.recognizerFoldCertificates P S T dss.flatten)),
    ("datatype-constructor", (["datatype-base", "datatype-atom", "datatype-list",
      "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
      "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case", "datatype-clauses",
      "datatype-case-sound", "datatype-den", "datatype-walk", "datatype-recognizer",
      "datatype-recognizer-fold"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.constructorCertificates P S T dss.flatten)),
    ("datatype-constructor-body", (["datatype-base", "datatype-atom", "datatype-list",
      "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
      "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case", "datatype-clauses",
      "datatype-case-sound", "datatype-den", "datatype-walk", "datatype-recognizer",
      "datatype-recognizer-fold", "datatype-constructor"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.constructorBodyCertificates P S T dss.flatten)),
    ("datatype-constructor-lam", (["datatype-base", "datatype-atom", "datatype-list",
      "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
      "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case", "datatype-clauses",
      "datatype-case-sound", "datatype-den", "datatype-walk", "datatype-recognizer",
      "datatype-recognizer-fold", "datatype-constructor", "datatype-constructor-body"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.constructorLamCertificates P S T dss.flatten)),
    ("datatype-constructor-nest", (["datatype-base", "datatype-atom", "datatype-list",
      "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
      "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case", "datatype-clauses",
      "datatype-case-sound", "datatype-den", "datatype-walk", "datatype-recognizer",
      "datatype-recognizer-fold", "datatype-constructor", "datatype-constructor-body",
      "datatype-constructor-lam"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.constructorNestCertificates P S T dss.flatten)),
    ("datatype-program", (["datatype-base"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.programCertificates P S T dss.flatten))]

set_option compiler.extract_closed false in
/-- The searches of the developments with certificates, each with its name, after those whose
certificates it continues from. Closed terms are not extracted, so that each search runs when it
is timed rather than when the program starts. -/
def searches : List (String × Search) :=
  List.append [("weakening", ([], fun _ ↦ inProgram Weakening.program fun P ↦
      (Weakening.certificate P).bind fun ds ↦ (Stored.certOf "weakening" ds).map ([·]))),
    ("substitution", ([], fun _ ↦ inProgram Substitution.program fun P ↦
      (Substitution.certificate P).bind fun ds ↦ (Stored.certOf "substitution" ds).map ([·]))),
    ("tree-cases", ([], fun _ ↦ inProgram TreeCases.program fun P ↦
      (TreeCases.certificate P).bind fun ds ↦ (Stored.certOf "tree-cases" ds).map ([·]))),
    ("expansion", ([], fun _ ↦ inProgram Expansion.program fun P ↦
      (Expansion.certificate P).bind fun ds ↦ (Stored.certOf "expansion" ds).map ([·]))),
    ("normalization", ([], fun _ ↦ inProgram Normalization.extended fun (P, S) ↦
      (Normalization.certificates P S).bind fun cs ↦ cs.mapM fun (n, ds) ↦ Stored.certOf n ds)),
    ("datatype-base", ([], fun _ ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
      Datatypes.certificates P S T)),
    ("datatype-atom", (["datatype-base"], fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
      Datatypes.atomCertificates P S T dss.flatten)),
    ("datatype-list", (["datatype-base", "datatype-atom"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.listCertificates P S T dss.flatten)),
    ("datatype-app", (["datatype-base", "datatype-atom", "datatype-list"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.appCertificates P S T dss.flatten)),
    ("datatype-stages", (["datatype-base", "datatype-atom", "datatype-list"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.stagesCertificates P S T dss.flatten)),
    ("datatype-lam", (["datatype-base", "datatype-atom", "datatype-list", "datatype-app",
        "datatype-stages"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.lamCertificates P S T dss.flatten)),
    ("datatype-apply", (["datatype-base", "datatype-atom", "datatype-list", "datatype-stages"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.applyCertificates P S T dss.flatten)),
    ("datatype-expansion", (["datatype-base", "datatype-atom", "datatype-list",
        "datatype-stages", "datatype-apply"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.expansionCertificates P S T dss.flatten)),
    ("datatype-assembly", (["datatype-base", "datatype-atom", "datatype-list", "datatype-stages",
        "datatype-apply", "datatype-expansion"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.assemblyCertificates P S T dss.flatten)),
    ("datatype-data", (["datatype-base", "datatype-atom", "datatype-list", "datatype-stages",
        "datatype-apply", "datatype-expansion", "datatype-assembly"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.dataCertificates P S T dss.flatten)),
    ("datatype-folds", (["datatype-base", "datatype-atom", "datatype-list", "datatype-stages",
        "datatype-apply", "datatype-expansion", "datatype-assembly"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.foldsCertificates P S T dss.flatten)),
    ("datatype-lists", (["datatype-base", "datatype-atom", "datatype-list", "datatype-stages",
        "datatype-apply", "datatype-expansion", "datatype-assembly", "datatype-app",
        "datatype-lam", "datatype-data", "datatype-folds"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.listsCertificates P S T dss.flatten)),
    ("datatype-datum", (["datatype-base", "datatype-atom", "datatype-list"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦ Datatypes.datumCertificates P S T dss.flatten)),
    ("datum-case", (["datatype-base", "datatype-atom", "datatype-list", "datatype-datum"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.datumCaseCertificates P S T dss.flatten)),
    ("datatype-decode", (["datatype-base", "datatype-atom", "datatype-list", "datatype-stages",
        "datatype-apply", "datatype-expansion", "datatype-assembly"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.decodeCertificates P S T dss.flatten)),
    ("decode-case", (["datatype-base", "datatype-atom", "datatype-list", "datatype-stages",
        "datatype-apply", "datatype-expansion", "datatype-assembly", "datatype-datum",
        "datatype-decode"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.decodeCaseCertificates P S T dss.flatten)),
    ("datatype-case", (["datatype-base", "datatype-atom", "datatype-list", "datatype-stages",
        "datatype-apply", "datatype-expansion", "datatype-assembly", "datatype-datum",
        "datatype-decode", "datatype-folds"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦ Datatypes.caseCertificates P S T dss.flatten)),
    ("datatype-clauses", (["datatype-base", "datatype-atom", "datatype-list", "datatype-stages",
        "datatype-apply", "datatype-expansion", "datatype-assembly", "datatype-datum",
        "datatype-decode", "datatype-folds", "datatype-case"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.clausesCertificates P S T dss.flatten)),
    ("datatype-case-sound", (["datatype-base", "datatype-atom", "datatype-list",
        "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
        "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case",
        "datatype-clauses"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.caseSoundCertificates P S T dss.flatten)),
    ("datatype-cata", (["datatype-base", "datatype-atom", "datatype-list",
        "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
        "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case",
        "datatype-clauses", "datatype-case-sound"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.cataCertificates P S T dss.flatten)),
    ("datatype-cata-clauses", (["datatype-base", "datatype-atom", "datatype-list",
        "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
        "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case",
        "datatype-clauses", "datatype-case-sound", "datatype-cata"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.cataClausesCertificates P S T dss.flatten)),
    ("datatype-cata-chain", (["datatype-base", "datatype-atom", "datatype-list",
        "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
        "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case",
        "datatype-clauses", "datatype-case-sound", "datatype-cata", "datatype-cata-clauses"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.cataChainCertificates P S T dss.flatten)),
    ("datatype-cata-sound", (["datatype-base", "datatype-atom", "datatype-list",
        "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
        "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case",
        "datatype-clauses", "datatype-case-sound", "datatype-cata", "datatype-cata-clauses",
        "datatype-cata-chain"], fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.cataSoundCertificates P S T dss.flatten)),
    ("datatype-cata-core", (["datatype-base", "datatype-atom", "datatype-list",
        "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
        "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case",
        "datatype-clauses", "datatype-case-sound", "datatype-cata", "datatype-cata-clauses",
        "datatype-cata-chain", "datatype-cata-sound"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.cataCoreCertificates P S T dss.flatten)),
    ("datatype-cata-src", (["datatype-base", "datatype-atom", "datatype-list",
        "datatype-stages", "datatype-apply", "datatype-expansion", "datatype-assembly",
        "datatype-datum", "datatype-decode", "datatype-folds", "datatype-case",
        "datatype-clauses", "datatype-case-sound", "datatype-cata", "datatype-cata-clauses",
        "datatype-cata-chain", "datatype-cata-sound", "datatype-cata-core"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.cataSrcCertificates P S T dss.flatten)),
    ("datatype-sound", (["datatype-base", "datatype-atom", "datatype-list", "datatype-stages",
        "datatype-apply", "datatype-expansion", "datatype-assembly", "datatype-app",
        "datatype-lam", "datatype-data", "datatype-folds", "datatype-lists"],
      fun dss ↦ inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.soundCertificates P S T dss.flatten)),
    ("datatype-closed", (["datatype-base", "datatype-atom", "datatype-list", "datatype-stages",
        "datatype-apply", "datatype-expansion", "datatype-assembly", "datatype-datum",
        "datatype-decode", "datatype-folds", "datatype-case", "datatype-clauses",
        "datatype-case-sound", "datatype-cata", "datatype-cata-clauses", "datatype-cata-chain",
        "datatype-cata-sound", "datatype-cata-core", "datatype-cata-src", "datum-case",
        "decode-case", "datatype-app", "datatype-lam", "datatype-data", "datatype-lists",
        "datatype-sound"], fun dss ↦
      inProgram Datatypes.extended3 fun (P, S, T) ↦
        Datatypes.closedCertificates P S T dss.flatten))] generatedSearches

end GebTests.Prototypes.FreeTopos.Certificates

end
