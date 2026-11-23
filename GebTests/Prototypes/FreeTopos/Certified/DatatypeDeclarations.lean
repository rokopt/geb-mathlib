/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Basic

set_option doc.verso true in
/-!
# The developments of the datatype language's soundness, read from their certificates

The developments of the datatype language's soundness, each read from its certificate under
{lit}`bootstrap/certificates/`, with the lists of the declarations a development continues from, in
the namespaces of the modules that check them. The module states no check: a module that checks
developments imports these declarations and no other check, so that Lake builds the checks at the
same time, and {lit}`GebTests.Prototypes.FreeTopos.Certified.DatatypeValid` composes them.

## Main definitions

Each namespace holds the developments its module checks, each a list of declarations, and the
lists of those a development continues from:

* {lit}`Datatype` — the developments of the datatype language's soundness at an atom.
* {lit}`DatatypeList` — the developments of the datatype language's soundness at the keywords'
  forms.
* {lit}`DatatypeForms` — the developments of the datatype language's soundness given the later
  keywords'.
* {lit}`DatatypeDatum` — the developments of the datatype language's soundness at datums and
  decodings.
* {lit}`DatatypeCase` — the developments of the datatype language's soundness at case analysis.
* {lit}`DatatypeCata` — the developments of the datatype language's soundness at structural
  recursion.
* {lit}`DatatypeGenerated` — the developments of the definitions the datatype language generates.
* {lit}`DatatypeClosed` — the developments of the datatype language's soundness at every tree.
* {lit}`DatatypeProgram` — the developments of the passes' runs over a program's forms.
* {lit}`DatatypeProgramKinds` — the developments of the steps of a whole program's soundness at
  definitions.
* {lit}`DatatypeProgramData` — the developments of the step of a whole program's soundness at a
  datatype.
* {lit}`DatatypeProgramSound` — the developments of the soundness of a whole program.

## Tags

internal language, datatypes, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified

open Geb Geb.FreeTopos

/-! The developments of the datatype language's soundness at an atom. -/

namespace Datatype

/-- The developments, read from their certificates, one after another. -/
def decls : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-base.cert") ++
    ofText (include_str "../../../../bootstrap/certificates/datatype-atom.cert")

end Datatype

/-! The developments of the datatype language's soundness at the keywords' forms. -/

namespace DatatypeList

/-- The developments, the soundness at the keywords' forms after the base's and the atom's. -/
def decls : List Internal.Decl :=
  Datatype.decls ++ ofText (include_str "../../../../bootstrap/certificates/datatype-list.cert")

end DatatypeList

/-! The developments of the datatype language's soundness given the later keywords'. -/

namespace DatatypeForms

/-- The development of the certificate {lit}`datatype-stages`. -/
def stages : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-stages.cert")

/-- The base, atoms and keywords' forms and the stage functions. -/
def upToStages : List Internal.Decl := DatatypeList.decls ++ stages

/-- The development of the certificate {lit}`datatype-apply`. -/
def apply : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-apply.cert")

/-- With the applications at expanded forms. -/
def upToApply : List Internal.Decl := upToStages ++ apply

/-- The development of the certificate {lit}`datatype-expansion`. -/
def expansion : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-expansion.cert")

/-- With the expansion of lists. -/
def upToExpansion : List Internal.Decl := upToApply ++ expansion

/-- The development of the certificate {lit}`datatype-assembly`. -/
def assembly : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-assembly.cert")

/-- With the keywords' arities and the atoms' applications. -/
def upToAssembly : List Internal.Decl := upToExpansion ++ assembly

/-- The development of the certificate {lit}`datatype-app`. -/
def app : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-app.cert")

/-- The development of the certificate {lit}`datatype-lam`. -/
def lam : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-lam.cert")

/-- The development of the certificate {lit}`datatype-data`. -/
def data : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-data.cert")

/-- The development of the certificate {lit}`datatype-folds`. -/
def folds : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-folds.cert")

/-- With the applications, the abstractions, the representations and the constants. -/
def upToFolds : List Internal.Decl := upToAssembly ++ app ++ lam ++ data ++ folds

/-- The development of the certificate {lit}`datatype-lists`. -/
def lists : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-lists.cert")

/-- The development of the certificate {lit}`datatype-sound`. -/
def sound : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-sound.cert")

end DatatypeForms

/-! The developments of the datatype language's soundness at datums and decodings. -/

namespace DatatypeDatum

/-- The development of the certificate {lit}`datatype-datum`. -/
def datum : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-datum.cert")

/-- The development of the certificate {lit}`datum-case`. -/
def datumCase : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datum-case.cert")

/-- The development of the certificate {lit}`datatype-decode`. -/
def decode : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-decode.cert")

/-- The development of the certificate {lit}`decode-case`. -/
def decodeCase : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/decode-case.cert")

end DatatypeDatum

/-! The developments of the datatype language's soundness at case analysis. -/

namespace DatatypeCase

/-- The developments the case analyses continue from. -/
def upToFolds : List Internal.Decl :=
  DatatypeForms.upToAssembly ++ DatatypeDatum.datum ++ DatatypeDatum.decode ++
    DatatypeForms.folds

/-- The development of the certificate {lit}`datatype-case`. -/
def caseDev : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-case.cert")

/-- With the walk of a clause's fields. -/
def upToCase : List Internal.Decl := upToFolds ++ caseDev

/-- The development of the certificate {lit}`datatype-clauses`. -/
def clauses : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-clauses.cert")

/-- With the chain of the clauses. -/
def upToClauses : List Internal.Decl := upToCase ++ clauses

/-- The development of the certificate {lit}`datatype-case-sound`. -/
def caseSound : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-case-sound.cert")

/-- With the soundness at a case analysis. -/
def upToCaseSound : List Internal.Decl := upToClauses ++ caseSound

end DatatypeCase

/-! The developments of the datatype language's soundness at structural recursion. -/

namespace DatatypeCata

/-- The development of the certificate {lit}`datatype-cata`. -/
def cata : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata.cert")

/-- With the walk of a structural recursion. -/
def upToCata : List Internal.Decl := DatatypeCase.upToCaseSound ++ cata

/-- The development of the certificate {lit}`datatype-cata-clauses`. -/
def cataClauses : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata-clauses.cert")

/-- With a clause of a structural recursion. -/
def upToCataClauses : List Internal.Decl := upToCata ++ cataClauses

/-- The development of the certificate {lit}`datatype-cata-chain`. -/
def cataChain : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata-chain.cert")

/-- With the chain of a structural recursion. -/
def upToCataChain : List Internal.Decl := upToCataClauses ++ cataChain

/-- The development of the certificate {lit}`datatype-cata-sound`. -/
def cataSound : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata-sound.cert")

/-- With the fold's convergence of a structural recursion. -/
def upToCataSound : List Internal.Decl := upToCataChain ++ cataSound

/-- The development of the certificate {lit}`datatype-cata-core`. -/
def cataCore : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata-core.cert")

/-- With the expanded form of a structural recursion. -/
def upToCataCore : List Internal.Decl := upToCataSound ++ cataCore

/-- The development of the certificate {lit}`datatype-cata-src`. -/
def cataSrc : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-cata-src.cert")

/-- With the source form of a structural recursion. -/
def upToCataSrc : List Internal.Decl := upToCataCore ++ cataSrc

end DatatypeCata

/-! The developments of the definitions the datatype language generates. -/

namespace DatatypeGenerated

/-- The development of the certificate {lit}`datatype-den`. -/
def den : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-den.cert")

/-- The developments the walk of a constructor's fields continues from. -/
def upToWalkBase : List Internal.Decl := DatatypeCase.upToCaseSound ++ den

/-- The development of the certificate {lit}`datatype-walk`. -/
def walk : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-walk.cert")

/-- With the walk of a constructor's fields. -/
def upToWalk : List Internal.Decl := upToWalkBase ++ walk

/-- The development of the certificate {lit}`datatype-recognizer`. -/
def recognizer : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-recognizer.cert")

/-- With the recognizers' decisions. -/
def upToRecognizer : List Internal.Decl := upToWalk ++ recognizer

/-- The development of the certificate {lit}`datatype-recognizer-fold`. -/
def recognizerFold : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-recognizer-fold.cert")

/-- With the recognizers' folds. -/
def upToRecognizerFold : List Internal.Decl := upToRecognizer ++ recognizerFold

/-- The development of the certificate {lit}`datatype-constructor`. -/
def ctor : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-constructor.cert")

/-- With the constructors' fields. -/
def upToCtor : List Internal.Decl := upToRecognizerFold ++ ctor

/-- The development of the certificate {lit}`datatype-constructor-body`. -/
def ctorBody : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-constructor-body.cert")

/-- With the constructors' bodies. -/
def upToCtorBody : List Internal.Decl := upToCtor ++ ctorBody

/-- The development of the certificate {lit}`datatype-constructor-lam`. -/
def ctorLam : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-constructor-lam.cert")

/-- With the abstractions of the constructors. -/
def upToCtorLam : List Internal.Decl := upToCtorBody ++ ctorLam

/-- The development of the certificate {lit}`datatype-constructor-nest`. -/
def ctorNest : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-constructor-nest.cert")

/-- With the constructors' definitions. -/
def upToCtorNest : List Internal.Decl := upToCtorLam ++ ctorNest

end DatatypeGenerated

/-! The developments of the datatype language's soundness at every tree. -/

namespace DatatypeClosed

/-- The developments the discharge continues from, in the order of its search. -/
def before : List Internal.Decl :=
  DatatypeCata.upToCataSrc ++ DatatypeDatum.datumCase ++ DatatypeDatum.decodeCase ++
    DatatypeForms.app ++ DatatypeForms.lam ++ DatatypeForms.data ++ DatatypeForms.lists ++
    DatatypeForms.sound

/-- The development of the certificate {lit}`datatype-closed`. -/
def closed : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-closed.cert")

end DatatypeClosed

/-! The developments of the passes' runs over a program's forms. -/

namespace DatatypeProgram

/-- The development of the certificate {lit}`datatype-base`. -/
def base : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-base.cert")

/-- The development of the certificate {lit}`datatype-program`. -/
def program : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-program.cert")

/-- The developments the soundness of a whole program continues from, in the order of its
search. -/
def before : List Internal.Decl :=
  DatatypeGenerated.upToCtorNest ++ program ++ DatatypeClosed.closed ++ DatatypeForms.app ++
    DatatypeForms.lam

/-- The developments of the runs of the passes over a program's forms, in the order of their
search. -/
def runs : List (List Internal.Decl) :=
  [ofText (include_str "../../../../bootstrap/certificates/datatype-program-read.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-expand.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-prefix.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-out-step.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-out.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-lists.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-lookup.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-kernel.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-inv.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-plain.cert")]

/-- With the passes' runs. -/
def upToRuns : List Internal.Decl := before ++ runs.flatten

end DatatypeProgram

/-! The developments of the steps of a whole program's soundness at definitions. -/

namespace DatatypeProgramKinds

/-- The developments of the invariant's parts and of the steps at the forms that write definitions,
in the order of their search. -/
def kinds : List (List Internal.Decl) :=
  [ofText (include_str "../../../../bootstrap/certificates/datatype-program-empty.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-forms.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-recs.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-occurs.cert"),
    ofText (include_str "../../../../bootstrap/certificates/datatype-program-refs.cert"),
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

/-- With the steps at the forms that write definitions. -/
def upToKinds : List Internal.Decl := DatatypeProgram.upToRuns ++ kinds.flatten

end DatatypeProgramKinds

/-! The developments of the step of a whole program's soundness at a datatype. -/

namespace DatatypeProgramData

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

/-- With the step at a datatype's declaration. -/
def upToData : List Internal.Decl := DatatypeProgramKinds.upToKinds ++ data.flatten

end DatatypeProgramData

/-! The developments of the soundness of a whole program. -/

namespace DatatypeProgramSound

/-- The developments of the kinds of forms and of the induction on a program's forms. -/
def defs : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-program-defs.cert")

/-- With the induction on a program's forms. -/
def upToDefs : List Internal.Decl := DatatypeProgramData.upToData ++ defs

/-- The development of the certificate {lit}`datatype-program-sound`. -/
def sound : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-program-sound.cert")

/-- With the program's soundness. -/
def upToSound : List Internal.Decl := upToDefs ++ sound

/-- The development of the certificate {lit}`datatype-program-closed`. -/
def closed : List Internal.Decl :=
  ofText (include_str "../../../../bootstrap/certificates/datatype-program-closed.cert")

end DatatypeProgramSound

end GebTests.Prototypes.FreeTopos.Certified

end
