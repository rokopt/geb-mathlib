/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCase
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeCase -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at structural recursion, proved in the internal language

The developments of the soundness at a structural recursion: the walk of a clause's fields beside
the suspended results, a clause, the chain, the fold's convergence, the expanded form and the source
form, each checked after the statements of the theorems it continues from
({lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeCase`).

## Main statements

* {lit}`cataSrc_valid` — their theorems are valid in every model of the program.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeCata

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)

/-- The development of the certificate {lit}`datatype-cata`. -/
def cata : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom cataChecked :
    checkedAfterIn extended3 (·.1.G) DatatypeCase.upToCaseSound cata = true

/-- With the walk of a structural recursion. -/
def upToCata : List Internal.Decl := DatatypeCase.upToCaseSound ++ cata

/-- The development of the certificate {lit}`datatype-cata-clauses`. -/
def cataClauses : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata-clauses.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom cataClausesChecked :
    checkedAfterIn extended3 (·.1.G) upToCata cataClauses = true

/-- With a clause of a structural recursion. -/
def upToCataClauses : List Internal.Decl := upToCata ++ cataClauses

/-- The development of the certificate {lit}`datatype-cata-chain`. -/
def cataChain : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata-chain.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom cataChainChecked :
    checkedAfterIn extended3 (·.1.G) upToCataClauses cataChain = true

/-- With the chain of a structural recursion. -/
def upToCataChain : List Internal.Decl := upToCataClauses ++ cataChain

/-- The development of the certificate {lit}`datatype-cata-sound`. -/
def cataSound : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata-sound.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom cataSoundChecked :
    checkedAfterIn extended3 (·.1.G) upToCataChain cataSound = true

/-- With the fold's convergence of a structural recursion. -/
def upToCataSound : List Internal.Decl := upToCataChain ++ cataSound

/-- The development of the certificate {lit}`datatype-cata-core`. -/
def cataCore : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata-core.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom cataCoreChecked :
    checkedAfterIn extended3 (·.1.G) upToCataSound cataCore = true

/-- With the expanded form of a structural recursion. -/
def upToCataCore : List Internal.Decl := upToCataSound ++ cataCore

/-- The development of the certificate {lit}`datatype-cata-src`. -/
def cataSrc : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata-src.cert")

set_option doc.verso false in
/-- The development checks in the extended program, after the theorems it continues from, as Lean's
evaluator decides. -/
evaluation_axiom cataSrcChecked :
    checkedAfterIn extended3 (·.1.G) upToCataCore cataSrc = true

/-- With the source form of a structural recursion. -/
def upToCataSrc : List Internal.Decl := upToCataCore ++ cataSrc

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)
  (m : ProgramModel.{v} PST.1.G)

include h

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

end GebTests.Prototypes.FreeTopos.Certified.DatatypeCata

end
