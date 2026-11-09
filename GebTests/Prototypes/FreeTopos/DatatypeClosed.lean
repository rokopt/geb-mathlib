/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeCataSrc
public import GebTests.Prototypes.FreeTopos.DatatypeSound
public meta import GebTests.Prototypes.FreeTopos.DatatypeCataSrc -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeSound -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at every tree

The soundness of the datatype language's stage-1 compiler at every tree, without hypotheses: the
keywords the soundness at every tree takes as hypotheses discharged, the datum's and the decoding's
at every number of elements and the others' as their developments state them.

## Main definitions

* {lit}`soundClosedThm` — the statement of the soundness at every tree, without hypotheses.
* {lit}`closedCertificates` — the development, stored as the certificate {lit}`datatype-closed`.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, soundness, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- The soundness at every list headed by the keyword {lit}`kw` ({name}`headedφ`), from that in the
context of its further elements ({name}`kwListThm`): its quantifier and hypothesis introduced. -/
def kwHeaded (P : Prog) (S : Defs) (T : Defs3) (kw : String) : Step :=
  (s!"headed/{kw}", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let φ := headedφ P S T kw
    let some d := (dAllI K.L <| dImpI K.L <|
        applyThm K (kwListName kw) (fun Γ ↦ [atPos 0 Γ])
          [fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ] fun Γ Φ ψ ↦
          K.byHyp (Φ.length - 1) Γ Φ ψ) [] [] φ
      | dbgTrace s!"headed/{kw}: not proved" fun _ ↦ none
    pure (⟨0, [], [], φ⟩, d))

/-- The statement of the soundness at every tree, the variable of index 0, without hypotheses. -/
def soundClosedThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  ⟨0, [treeTy], [], datatypeφ P S T⟩

/-- The soundness at every tree, without hypotheses ({name}`soundClosedThm`): {name}`soundThm` at
the keywords' soundness, of the steps each names. -/
def soundClosed (P : Prog) (S : Defs) (T : Defs3) (headed : List String) : Step :=
  ("soundClosed", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let last : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let a := soundClosedThm P S T
    let some d := applyThm K "sound" (fun _ ↦ [v 0])
        (headed.map fun nm ↦ K.cutThm nm (fun _ ↦ []) last) last a.ctx a.hyps a.concl
      | dbgTrace "soundClosed: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness at every tree without hypotheses: the datum's and the
decoding's at every number of elements, of which only their forms' are not refuted
({name}`kwList`), then the discharge. -/
def closedDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [kwList P S T "Typing.kwDatum" 2 "datumCase", kwList P S T "Typing.kwDecode" 4 "decodeCase",
    kwHeaded P S T "Typing.kwDatum", kwHeaded P S T "Typing.kwDecode",
    soundClosed P S T ["headed/Typing.kwDatum", "headed/Typing.kwDecode", "caseHeaded",
      "cataHeaded"]]

/-- The soundness at every tree without hypotheses, after the developments of each keyword's. -/
def closedCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := caseNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (caseDev P S T).map (·.1) ++ (clausesDev P S T).map (·.1) ++
    (caseSoundDev P S T).map (·.1) ++ (cataDev P S T).map (·.1) ++
    (cataClausesDev P S T).map (·.1) ++ (cataChainDev P S T).map (·.1) ++
    (cataSoundDev P S T).map (·.1) ++ (cataCoreDev P S T).map (·.1) ++
    (cataSrcDev P S T).map (·.1) ++ ["datumCase"] ++
    ([atomEta P S, mapAppend P S T, mapAppendEq P S T] ++ expansionEqs P T ++
      [decodeCase P S T]).map (·.1) ++
    (appDev3 P S T).map (·.1) ++ (lamDev3 P S T).map (·.1) ++ (dataDev3 P S T).map (·.1) ++
    (listsDev3 P S T).map (·.1) ++ (soundDev3 P S T).map (·.1))
    "datatype-closed" (closedDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
