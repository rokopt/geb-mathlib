/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeProgramCtor
public meta import GebTests.Prototypes.FreeTopos.DatatypeProgramCtor -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a whole program at a datatype's declaration

The step of a whole program's soundness ({lit}`passesForms`) at a form that declares a datatype.
The expansion declares the datatype and its constructors and writes a block of typed forms: the
datatype's node, the definition of each constructor, and the datatype's marker, which holds an
entry for each constructor. The hypotheses at the states of the passes ({lit}`Passes.hyps`) are
followed through the block. The node read leaves states at which the typing environment has the
datatype's name and the reader the abbreviation of it as the trees' type. A constructor's
definition is sound at the states it is read at ({lit}`ctorSoundAt`, {lit}`ctorSoundVarAt`),
where the typing reads the datatype's atom as the datatype and the marker, which the typing
checks before the other forms, has the constructor's entry; read, it leaves states of which the
hypotheses hold again, as any definition written does ({lit}`writtenInv`). At the marker, the
recognizers' insertion gives the datatype's recognizer where the program's forms refer to it,
and no form where they do not: the recognizer the writer gives denotes a function deciding
membership ({lit}`recognizerDen`), so that the recognizers' agreement holds at the datatypes of
the typing environment, those before the block and the marker's. The constructors' definitions
are read by induction on the constructors, at all states, with the facts of the block that the
steps at its forms preserve.

## Main definitions

* {lit}`Passes.declared` — the states after a datatype's node is read.
* {lit}`blockFacts`, {lit}`blockStatics` — the facts of a datatype's block.
* {lit}`blockHyps` — the hypotheses of the soundness within a block, at a list of constructors.

## Main statements

* {lit}`dataInv` — the hypotheses at the states are preserved by a datatype's node read.
* {lit}`markerSkipped`, {lit}`markerReadAt` — they are preserved by a marker, where the
  program's forms do not refer to its datatype's recognizer and where they do.
* {lit}`recognizerAt` — a marker's recognizer and its denotation, at the states.
* {lit}`blockEnd` — the soundness at the forms that remain, at a block's marker.
* {lit}`blockCtor` — the soundness within a block, a step at a constructor's definition.
* {lit}`ctorsInv` — the soundness within a block, by induction on the constructors.
* {lit}`stepData` — the step at a datatype's declaration.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- The erasure of a datatype's node is the abbreviation of the datatype's atom as the trees'
type. In the context of the atom. -/
def eraseData (P : Prog) (S : Defs) : Step :=
  foldedEq P S "eraseData" "Datatype.eraseForm" [treeTy]
    (pc P "Datatype.eraseForm" [pc P "Typing.tData" [v 0]])
    (listNode [pc P "Datatype.aDeftype" [], v 0, pc P "Datatype.aT" []])

/-- The aliases stay type abbreviations of the reader's ({name}`aliasTysT`) under an
abbreviation before the others: a name is the abbreviation's, or abbreviated as before. In the
context of the abbreviation's type, the name, the abbreviations and the declarations. -/
def aliasTysWeaken (P : Prog) (S : Defs) : Step :=
  ("aliasTysWeaken", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, numsEqNames⟩
    let L := K.L
    let equalT ← primT Kernel.Prim.equal
    let Γ₀ := [treeTy, treeTy, list treeTy, list treeTy]
    let (ty, nm, tys, dv) := (v 0, v 1, v 2, v 3)
    let thm : Internal.Thm := ⟨0, Γ₀, [aliasTysT P dv tys],
      aliasTysT P dv (consT treeTy (abbrevT P nm ty) tys)⟩
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (nmA, nA) := (at_ 2, at_ 4)
    let some d := (dAllI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
        let hAl := Φ₁.length - 1
        decideIn K (fun Γ ↦ apps equalT [nA Γ, nmA Γ])
          (stage "aliasTysWeaken: abbreviated before" fun Γ Φ ψ ↦
            dAllE L K.G K.E 0 (nA Γ) (K.impE (K.byHyp hAl) <| fun Γ Φ ψ ↦
              K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
          (stage "aliasTysWeaken: the name abbreviated" (K.solve 3)) Γ₁ Φ₁ ψ₁)
        thm.ctx thm.hyps thm.concl
      | dbgTrace "aliasTysWeaken: not proved" fun _ ↦ none
    pure (thm, d))

/-- The states after a datatype's node of an atom is read, given the pending forms after it:
the typing environment has the datatype's name after the datatypes' names, without a
rejection, and the reader has the abbreviation of the name as the trees' type before the type
abbreviations. -/
def Passes.declared (P : Prog) (s : Passes) (d ws : Term) : Passes :=
  { s with
    env := pc P "Typing.withNoms" [s.env, pc P "Typing/Names.append"
      [pc P "Typing.envNoms" [s.env], pc P "Typing/Names.single" [pc P "Typing.atomName" [d]]]]
    rej := pc P "Typing/OName.nothing" []
    tys := consT treeTy (abbrevT P (pc P "Reader.nameOf" [d])
      (pc P "Prelude.get" [pc P "Reader.readType" [s.tys, pc P "Datatype.aT" []]])) s.tys
    ws := some ws }

/-- The hypotheses at the states are preserved by a datatype's node read: the node of an atom,
before pending forms, leaves states ({name}`Passes.declared`) of which the hypotheses hold
again, and whose conclusion gives that at the states before. The typing's step
({lit}`checkData`) has the datatype's name after the datatypes' names; the node's erasure
({name}`eraseData`) is the abbreviation of the atom as the trees' type, at which the reader's
step ({lit}`readDeftype`) has the abbreviation before the type abbreviations, the atom's name
fresh ({lit}`freshParts`). The invariant reads neither the datatypes' names nor, but for the
aliases' abbreviations ({name}`aliasTysWeaken`), the type abbreviations. The conclusion has
also that the atom is one, and that its name is not reserved and abbreviated no type. In the
context of the atom, the pending forms after, the forms that remain, the states and the
recognizers' environment. -/
def dataInv (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("dataInv", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseData", "recAtThree"]⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"dataInv @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "dataInv: no partition" fun _ ↦ none
    let tData (d : Term) : Term := pc P "Typing.tData" [d]
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let s : Passes := { passesAt 3 (v 2) with
      ws := some (consT treeTy (tData (v 0)) (v 1)), recEnv := some (v 12) }
    let Γ₀ := [treeTy, Ls, Ls] ++ passesCtx T ++ [T.envTy]
    let s' := s.declared P (v 0) (v 1)
    let nm := pc P "Reader.nameOf" [v 0]
    let fresh : List Term := [truth o (pc P "Reader.isAtom" [v 0]),
      notTest o (isSome (pc P "Reader.indexOf" [nm, pc P "Reader.reservedNames" []])),
      notTest o (isSome (pc P "Reader.lookupAbbrev" [nm, s.tys]))]
    let a : Internal.Thm := ⟨0, Γ₀, s.hyps P S T X₀, conjAll o (s'.hyps P S T X₀ ++
      [Internal.Logic.imp o (s'.concl P T X₀) (s.concl P T X₀)] ++ fresh)⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (dA, wsA, esA) := (at_ 0, at_ 1, at_ 2)
    let (termsA, namesA, numsA, tysA, rA, EA, dvA) :=
      (at_ 5, at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11)
    let sA (Γ : List Tree) : Passes := { passesAt (3 + (Γ.length - Γ₀.length)) (esA Γ) with
      ws := some (consT treeTy (tData (dA Γ)) (wsA Γ)), recEnv := some (at_ 12 Γ) }
    let restA (Γ : List Tree) : Passes := { sA Γ with ws := some (wsA Γ) }
    let nmA (Γ : List Tree) : Term := pc P "Reader.nameOf" [dA Γ]
    let aT := pc P "Datatype.aT" []
    let aDeftype := pc P "Datatype.aDeftype" []
    let kA (Γ : List Tree) : Term := listNode [aDeftype, dA Γ, aT]
    let stA (Γ : List Tree) : Term := progState (tysA Γ) (numsA Γ) (namesA Γ) (termsA Γ)
    let rsA (Γ : List Tree) : Term := flatT P (Term.snd ((restA Γ).inserted P))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    let unfoldBoth := unfoldBothK K
    -- the hypotheses' indices
    let (hX, hC, hO, hR, hK, hRej, hGlob, hNums, hNames, hKws, hLen, hRecs) :=
      (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)
    let (hP, hOcc, hIns, hUsed, hUser, hSorts, hAl, hAlKw, hAlTys, hMs, hMk, hStatic) :=
      (12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23)
    -- the hypotheses at the states the steps leave
    let apply (iAtom iFresh iO : ℕ) : Deducer := at' "the states after" <|
      normHyps K [hOcc] <| K.conjE <| last fun iOccRest ↦
      normHyps K [hMk] <| K.conjE <| last fun iMkRest ↦
      applyThm K "freshParts" (fun Γ ↦ [nmA Γ, namesA Γ, numsA Γ, tysA Γ])
        [stage "dataInv: fresh" (hypOr iFresh)] <| K.conjE <| K.conjE <| K.conjE <|
      fun Γ₅ Φ₅ ψ₅ ↦
      let (iUnres, iNotTys) := (Φ₅.length - 6, Φ₅.length - 2)
      (applyThm K "aliasTysWeaken" (fun Γ ↦ [pc P "Prelude.get"
            [pc P "Reader.readType" [tysA Γ, aT]], nmA Γ, tysA Γ, dvA Γ])
          [stage "dataInv: the aliases abbreviated before" (hypOr hAlTys)] <|
        last fun iAlTys' ↦ conjIs L
          [stage "dataInv: the rest expands" (K.byHyp hX),
            stage "dataInv: the rest checks" (K.byHyp hC),
            stage "dataInv: the rest's recognizers" (hypOr iO),
            stage "dataInv: the rest reads" (K.byHyp hR),
            stage "dataInv: the kernel checks" (K.byHyp hK),
            stage "dataInv: no rejection" (dImpI L (lastFalse K)),
            stage "dataInv: related after" (unfoldBoth (T.q + 2) hGlob),
            stage "dataInv: the numerals after" (unfoldBoth (T.q + 3 + 2 * nFolds) hNums),
            stage "dataInv: the names" (hypOr hNames),
            stage "dataInv: the keywords" (hypOr hKws),
            stage "dataInv: the lengths" (hypOr hLen),
            stage "dataInv: the recognizers" (unfoldBoth (T.q + 6 + 2 * nFolds) hRecs),
            stage "dataInv: the bodies after" (K.byHyp hP),
            stage "dataInv: the occurrences after" (hypOr iOccRest),
            stage "dataInv: the recognizers referred to" (hypOr hIns),
            stage "dataInv: the names' occurrences" (hypOr hUsed),
            stage "dataInv: the names' origin" (hypOr hUser),
            stage "dataInv: no sort after" (hypOr hSorts),
            stage "dataInv: the aliases after" (hypOr hAl),
            stage "dataInv: the aliases of types read first" (hypOr hAlKw),
            stage "dataInv: the aliases abbreviated" (hypOr iAlTys'),
            stage "dataInv: the markers" (normHyps K [hMs] K.byNorm),
            stage "dataInv: the markers that remain" (hypOr iMkRest),
            stage "dataInv: the markers and the numerals" (hypOr hStatic),
            stage "dataInv: the conclusion" (dImpI L (last K.byHyp)),
            stage "dataInv: an atom" (K.byHyp iAtom),
            stage "dataInv: not reserved" (hypOr iUnres),
            stage "dataInv: no type abbreviated" (hypOr iNotTys)]) Γ₅ Φ₅ ψ₅
    -- the reader's step
    let reader : Deducer := at' "the reader" <|
      applyThm K "someTruth" (fun Γ ↦ [Term.fst ((restA Γ).inserted P)])
        [stage "dataInv: the recognizers' insertion" (K.byHyp hO)] <| last fun iO ↦
      applyThm K "readPrefix" (fun Γ ↦ [rsA Γ, pc P "Reader.progStep" [stA Γ, kA Γ]])
        [stage "dataInv: the reader's run" (K.byHyp hR)] <| at' "the reader's step" <|
      applyThm K "readDeftype" (fun Γ ↦ [aT, dA Γ, aDeftype, termsA Γ, namesA Γ, numsA Γ,
          tysA Γ])
        [stage "dataInv: the reader's test of a definition" (dImpI L (lastFalse K)),
          stage "dataInv: the reader's keyword" (K.solve 3),
          stage "dataInv: the reader's step" dHyp] <|
      K.conjE <| K.conjE <| K.conjE <| fun Γ Φ ψ ↦
        let (iAtom, iFresh, iRead) := (Φ.length - 6, Φ.length - 4, Φ.length - 1)
        normHyps K [iRead] (apply iAtom iFresh iO) Γ Φ ψ
    -- the typing's step
    let typing : Deducer := at' "the typing" <|
      applyThm K "checkData" (fun Γ ↦ [dA Γ, rA Γ, EA Γ])
        [stage "dataInv: no rejection before" (hypOr hRej)] <|
      last fun iCheck ↦ normHyps K [iCheck] reader
    let _ := (EA, sA)
    let some d := typing a.ctx a.hyps a.concl
      | dbgTrace "dataInv: not proved" fun _ ↦ none
    pure (a, d))

/-- The program of the steps at a marker: the passes' steps kept folded
({name}`passProg`), and the writer's recognizer. -/
def markerProg (P : Prog) : Prog :=
  { passProg P with folded := (passProg P).folded ++ ["Recognize.recognizer"] }

/-- A marker of a datatype's atom and its constructors' entries: the node of the markers' label
over them. -/
def markerT (d xs : Term) : Term := nodeT (Term.pair (numeral 9) (consT treeTy d xs))

/-- The erasure of a marker is the marker. In the context of the datatype's atom and the
constructors' entries. -/
def eraseMarker (P : Prog) (S : Defs) : Step :=
  foldedEq P S "eraseMarker" "Datatype.eraseForm" [treeTy, list treeTy]
    (pc P "Datatype.eraseForm" [markerT (v 0) (v 1)]) (markerT (v 0) (v 1))

/-- The recognizers' insertion at a marker, unfolded: its sides in the normal forms of the rules
at a marker's steps ({name}`markerProg`), the left with the insertion folded. In the context of
the datatype's atom, the constructors' entries, the program's forms and its markers. -/
def recAtMarker (P : Prog) (S : Defs) : Step :=
  ("recAtMarker", fun ix E ↦ do
    let K : Kit := ⟨markerProg P, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [treeTy, Ls, Ls, Ls]
    let lhs := pc P "Recognize.recognizersAt" [v 3, v 2, markerT (v 0) (v 1)]
    let unfolded := K.rules [] ++ [.delta (P.idx "Recognize.recognizersAt")]
    let some l := nfE K.G K.E (K.rules []) Γ lhs | dbgTrace "recAtMarker: left" fun _ ↦ none
    let some r := nfE K.G K.E unfolded Γ lhs | dbgTrace "recAtMarker: right" fun _ ↦ none
    let some d := byMode .full K.G K.E 0 unfolded Γ [] l r
      | dbgTrace "recAtMarker: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- A predicate of each of a list of names holds of a name with an index among them: by
induction on the names; at a construction the name is the head, of which the predicate holds
({lit}`equalSound`), or has an index among the rest. In the context of the names, under the
predicate and the name. -/
def allIndexed (P : Prog) (S : Defs) : Step :=
  ("allIndexed", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let Pr := exp treeTy omega
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let idx (x xs : Term) : Term := pc P "Reader.indexOf" [x, xs]
    -- under the quantifiers: the name v0, the predicate v1, the names v2
    let φ := Internal.Logic.all o Pr (Term.lam Pr (Internal.Logic.all o treeTy (Term.lam treeTy
      (Internal.Logic.imp o (S.allL (v 1) (v 2)) (Internal.Logic.imp o
        (truth o (isSome (idx (v 0) (v 2)))) (Term.app (v 1) (v 0)))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let intro (k : ℕ → ℕ → Deducer) : Deducer := dAllI L <| dAllI L <| dImpI L <| dImpI L
      fun Γ Φ ψ ↦ k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ
    let base : Deducer := intro fun _ hIdx ↦ K.hypFalse hIdx
    -- a construction: the head v(0), the tail v(1), the predicate v(2), the name v(3)
    let step : Deducer := intro fun hAll hIdx ↦
      let (b, tl, pr, x) := (at_ 0, at_ 1, at_ 2, at_ 3)
      normHyps K [hAll] <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (iHead, iTail) := (Φ₂.length - 2, Φ₂.length - 1)
        (decideIn K (fun Γ ↦ apps equalT [x Γ, b Γ])
          (decideIn K (fun Γ ↦ isSome (idx (x Γ) (tl Γ)))
            (stage "allIndexed: no index" (K.hypFalse hIdx))
            (stage "allIndexed: among the rest" fun Γ Φ ψ ↦
              dAllE L K.G K.E 0 (pr Γ) (K.allEΓ x <| K.impE (K.byHyp iTail) <|
                K.impE (K.solve 3) <| fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ))
          (stage "allIndexed: the head" <|
            K.cutThm "equalSound" (fun Γ ↦ [x Γ]) <| K.allEΓ b <| K.impE (K.solve 3) <|
            normLastK K <| K.byHyp iHead)) Γ₂ Φ₂ ψ₂
    listInduction "allIndexed" φ base step)

/-- The hypotheses at the states are preserved by a marker to whose datatype's recognizer the
program's forms do not refer: the marker, before pending forms, leaves the states as they are,
the recognizers' environment now the typing's, whose datatypes are those of the recognizers'
environment before and the marker's. The typing checks the markers before the other forms, the
marker's erasure is the marker ({name}`eraseMarker`), and the recognizers' insertion gives no
form for it ({name}`recAtMarker`). The recognizers' agreement and the recognizers referred to
hold at the marker's datatype in the absence of its recognizer's name among the names, each of
whose atoms occurs in the forms ({name}`allIndexed`). In the context of the characters of the
datatype's atom, the constructors' entries, the pending forms after, the forms that remain,
the states and the recognizers' environment. -/
def markerSkipped (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("markerSkipped", fun ix E ↦ do
    let K : Kit := ⟨markerProg P, S, E, ix, ["eraseMarker", "recAtMarker"] ++ lookupEqNames⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"markerSkipped @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "markerSkipped: no partition" fun _ ↦ none
    let atom (cs : Term) : Term := nodeT (Term.pair (numeral 1) cs)
    let s : Passes := { passesAt 4 (v 3) with
      ws := some (consT treeTy (markerT (atom (v 0)) (v 1)) (v 2)), recEnv := some (v 13) }
    let Γ₀ := [Ls, Ls, Ls, Ls] ++ passesCtx T ++ [T.envTy]
    let s' : Passes := { s with ws := some (v 2), recEnv := none }
    let noms (e : Term) : Term := pc P "Typing.envNoms" [e]
    let recName (d : Term) : Term := pc P "Typing.recognizerName" [d]
    let dn := pc P "Typing.atomName" [atom (v 0)]
    let hyps := s.hyps P S T X₀ ++ [Term.eq (noms s.env) (namesSnoc P (noms (v 13)) dn),
      notTest o (occInT P (memberAtomT P dn) s.fs)]
    let a : Internal.Thm := ⟨0, Γ₀, hyps, conjAll o (s'.hyps P S T X₀ ++
      [Internal.Logic.imp o (s'.concl P T X₀) (s.concl P T X₀)])⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (xsA, wsA, esA, fsA, namesA, ErA) := (at_ 1, at_ 2, at_ 3, at_ 4, at_ 7, at_ 13)
    let dA (Γ : List Tree) : Term := atom (at_ 0 Γ)
    let dnA (Γ : List Tree) : Term := pc P "Typing.atomName" [dA Γ]
    let sA (Γ : List Tree) : Passes := { passesAt (4 + (Γ.length - Γ₀.length)) (esA Γ) with
      ws := some (consT treeTy (markerT (dA Γ) (xsA Γ)) (wsA Γ)), recEnv := some (ErA Γ) }
    let restA (Γ : List Tree) : Passes := { sA Γ with ws := some (wsA Γ) }
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    let unfoldBoth := unfoldBothK K
    -- the hypotheses' indices
    let (hX, hC, hO, hR, hK, hRej, hGlob, hNums, hNames, hKws, hLen, hRecs) :=
      (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)
    let (hP, hOcc, hIns, hUsed, hUser, hSorts, hAl, hAlKw, hAlTys, hMs, hMk, hStatic) :=
      (12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23)
    let (hNoms, hSkip) := (24, 25)
    let referred (Γ : List Tree) : Term := occInT P (memberAtomT P (dnA Γ)) (fsA Γ)
    let recsIdx := T.q + 6 + 2 * nFolds
    -- at a datatype of the environment, the variable of the context of {lit}`n` variables,
    -- under the hypothesis of index {lit}`hHas`: one of the recognizers' environment's, by
    -- {lit}`old`, or the marker's, by {lit}`new` under the datatype's equation with it
    let cases (n hHas : ℕ) (old new : Deducer) : Deducer :=
      let dv (Γ : List Tree) : Term := v (Γ.length - n)
      decideIn K (fun Γ ↦ hasT P (dv Γ) (noms (ErA Γ)))
        (K.cutThm "hasSnocCases" (fun Γ ↦ [noms (ErA Γ)]) <| K.allEΓ dv <| K.allEΓ dnA <|
          K.impE (at' "a datatype after the marker's"
            (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ hHas) .full) hHas
              (K.norm dHyp) Γ Φ ψ)) <|
          K.impE (dImpI L (lastFalse K)) <| last fun iEq ↦
          K.cutThm "equalSymm" (fun Γ ↦ [dv Γ, dnA Γ]) <| K.impE (K.byHyp iEq) <|
          last fun iEq' ↦ K.cutThm "equalSound" (fun Γ ↦ [dv Γ]) <| K.allEΓ dnA <|
          K.impE (K.byHyp iEq') <| normLastK K new)
        old
    let apply (iO : ℕ) : Deducer := at' "the states after" <|
      normHyps K [hOcc] <| K.conjE <| last fun iOccRest ↦
      normHyps K [hMk] <| K.conjE <| last fun iMkRest ↦
      let recs : Deducer := dRwBy (evalRw K.G K.E [.delta recsIdx] .head) <|
        dAllI L <| dImpI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
        let (hHas, hIdx, n) := (Φ₁.length - 2, Φ₁.length - 1, Γ₁.length)
        cases n hHas
          (at' "a datatype before" <|
            dRwHyp (evalRw K.G K.E [.delta recsIdx] .head) hRecs <|
            K.allEΓ (fun Γ ↦ v (Γ.length - n)) <| K.impE (K.solve 3) <|
            K.impE (K.byHyp hIdx) <| last K.byHyp)
          (at' "the marker's datatype" <|
            K.cutThm "allIndexed" (fun Γ ↦ [namesA Γ]) <|
            K.allEΓ (fun Γ ↦ usedPred P (fsA Γ)) <| K.allEΓ (fun Γ ↦ recName (dnA Γ)) <|
            K.impE (hypOr hUsed) <| K.impE (K.byHyp hIdx) <| last fun iUsed ↦
            dImpE L hSkip (at' "referred to" (K.byHyp iUsed)) (dFalse L dHyp)) Γ₁ Φ₁ ψ₁
      let ins : Deducer := dAllI L <| dImpI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
        let (hHas, hRef, n) := (Φ₁.length - 2, Φ₁.length - 1, Γ₁.length)
        cases n hHas
          (at' "a recognizer referred to before" fun Γ Φ ψ ↦
            dAllE L K.G K.E hIns (v (Γ.length - n)) (K.impE (K.solve 3) <|
              K.impE (K.byHyp hRef) <| last K.byHyp) Γ Φ ψ)
          (at' "the marker's recognizer referred to" <|
            dImpE L hSkip (K.byHyp hRef) (dFalse L dHyp)) Γ₁ Φ₁ ψ₁
      conjIs L
        [stage "markerSkipped: the rest expands" (K.byHyp hX),
          stage "markerSkipped: the rest checks" (K.byHyp hC),
          stage "markerSkipped: the rest's recognizers" (hypOr iO),
          stage "markerSkipped: the rest reads" (K.byHyp hR),
          stage "markerSkipped: the kernel checks" (K.byHyp hK),
          stage "markerSkipped: no rejection" (hypOr hRej),
          stage "markerSkipped: related" (unfoldBoth (T.q + 2) hGlob),
          stage "markerSkipped: the numerals" (hypOr hNums),
          stage "markerSkipped: the names" (hypOr hNames),
          stage "markerSkipped: the keywords" (hypOr hKws),
          stage "markerSkipped: the lengths" (hypOr hLen),
          stage "markerSkipped: the recognizers" recs,
          stage "markerSkipped: the bodies" (K.byHyp hP),
          stage "markerSkipped: the occurrences after" (hypOr iOccRest),
          stage "markerSkipped: the recognizers referred to" ins,
          stage "markerSkipped: the names' occurrences" (hypOr hUsed),
          stage "markerSkipped: the names' origin" (hypOr hUser),
          stage "markerSkipped: no sort" (hypOr hSorts),
          stage "markerSkipped: the aliases" (hypOr hAl),
          stage "markerSkipped: the aliases of types read first" (hypOr hAlKw),
          stage "markerSkipped: the aliases abbreviated" (hypOr hAlTys),
          stage "markerSkipped: the markers" (hypOr hMs),
          stage "markerSkipped: the markers that remain" (hypOr iMkRest),
          stage "markerSkipped: the markers and the numerals" (hypOr hStatic),
          stage "markerSkipped: the conclusion" (dImpI L (last K.byHyp))]
    let some d := (normHyps K [hNoms] <|
        decideIn K referred
          (applyThm K "someTruth" (fun Γ ↦ [Term.fst ((restA Γ).inserted P)])
            [stage "markerSkipped: the recognizers' insertion" (K.byHyp hO)] <|
            last fun iO ↦ apply iO)
          (at' "referred to" (refuteNot K hSkip))) a.ctx a.hyps a.concl
      | dbgTrace "markerSkipped: not proved" fun _ ↦ none
    pure (a, d))

/-- A name is a primitive's: closed, by normalization of the presence of its index among the
primitives' names ({name}`isSomeIndexOfCons`, {name}`truthOfEq`), the left disjunct of the
test the reader's names exclude. -/
def primNamed (P : Prog) (S : Defs) (name : String) (n : Term) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, ["isSomeIndexOfCons", "indexOfNil"]⟩
    let equalT ← primT Kernel.Prim.equal
    let prim := pc P "Prelude.isSome" [pc P "Reader.indexOf" [n, pc P "Reader.primNames" []]]
    let unit := apps equalT [n, pc P "Reader.kwUnitValue" []]
    let φ := truth P.o (pc P "Prelude.or" [prim, unit])
    let byTest : Deducer := applyThm K "truthOfEq" (fun _ ↦ [prim]) [fun Γ Φ ψ ↦
        dEq (fun Γ _ t u ↦ byMode .full K.G K.E 0 (K.rules []) Γ [] t u) Γ Φ ψ] dHyp
    let some d := (applyThm K "orLeftT" (fun _ ↦ [unit, prim]) [byTest] dHyp) [] [] φ
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (⟨0, [], [], φ⟩, d))

/-- The names of the atoms the writer's terms name, each with the name of the lemma that it is
excluded from the abbreviated names. -/
def writerExcludedNames (P : Prog) : List (Term × String) :=
  writerAtoms.zipIdx.map fun (a, i) ↦
    (atomNameT (pc P s!"Recognize.{a}" []), s!"writerExcluded{i}")

/-- The names of the primitives the writer's terms name, each with the name of the lemma that
it is a primitive's. -/
def writerPrimNames (P : Prog) : List (Term × String) :=
  writerPrims.zipIdx.map fun (a, i) ↦ (atomNameT (pc P s!"Recognize.{a}" []), s!"writerPrim{i}")

/-- The development of the writer's atoms: each excluded from the abbreviated names, each
primitive's name a primitive's. -/
def writerAtomsDev (P : Prog) (S : Defs) : List Step :=
  (writerExcludedNames P).map (fun (n, nm) ↦ atomExcluded P S nm n) ++
    (writerPrimNames P).map fun (n, nm) ↦ primNamed P S nm n

/-- A datatype whose constructors the typing reads off the markers has an index among the
markers' names: without one the reading is of no marker. In the context of the constructors,
the datatype's atom and the markers. -/
def ctorsIndexed (P : Prog) (S : Defs) : Step :=
  ("ctorsIndexed", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ₀ := [Ls, treeTy, Ls]
    let ctors (ms d : Term) : Term := pc P "Typing.markerCtors" [ms, d]
    let present (ms d : Term) : Term := pc P "Prelude.isSome" [markerIdx P d ms]
    let a : Internal.Thm := ⟨0, Γ₀,
      [Term.eq (ctors (v 2) (v 1)) (Term.pair (leafT (numeral 1)) (v 0))],
      truth P.o (present (v 2) (v 1))⟩
    let (msA, dA) := (atPos 0, atPos 1)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let some d := (cutBy (fun Γ ↦ truth P.o (Term.fst (ctors (msA Γ) (dA Γ))))
        (dRwBy (evalRw K.G K.E [.hyp 0] .full) (K.solve 3)) <| last fun iRead ↦
        decideIn K (fun Γ ↦ present (msA Γ) (dA Γ))
          (stage "ctorsIndexed: no index" (K.hypFalse iRead)) (K.solve 3))
        a.ctx a.hyps a.concl
      | dbgTrace "ctorsIndexed: not proved" fun _ ↦ none
    pure (a, d))

/-- A marker's recognizer at states of which the invariant's parts hold, where the writer gives
one and the marker's datatype has an index among the markers' names: the definition and its
denotation ({lit}`recognizerDen`), in the empty scope and environment. Of that lemma's
hypotheses, no marker's datatype is named as the trees' type, the numerals read as numbers
({name}`numOfKws`), the atoms the writer's terms name are excluded from the abbreviated names,
and the primitives' names from the reader's names. In the context of the marker, the markers,
the type abbreviations, the names, the numeral abbreviations and the relation's context. -/
def recognizerAt (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("recognizerAt", fun ix E ↦ do
    let K : Kit := ⟨markerProg P, S, E, ix, []⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let some (Internal.Entry.language c) := E[ix "recognizerDen"]?
      | dbgTrace "recognizerAt: the recognizer's denotation is absent" fun _ ↦ none
    let Γ₀ := [treeTy, Ls, Ls, Ls, Ls, Defs3.ctxTy]
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (mA, msA, tysA, namesA, numsA, RA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5)
    let σ (Γ : List Tree) : List Term :=
      [mA Γ, msA Γ, nil, nil, tysA Γ, namesA Γ, numsA Γ, RA Γ]
    let inst (t : Term) : Term := Internal.instTerm [] (σ Γ₀) t
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let hyps := [inst (c.hyps.headD Term.star), T.kwsT (numsA Γ₀), T.namesT (namesA Γ₀),
      staticT P (msA Γ₀), digitsFixedT P, inst (c.hyps.getLastD Term.star)]
    let (hRec, hKws, hNames, hStatic, hDigits, hIdx) := (0, 1, 2, 3, 4, 5)
    let a : Internal.Thm := ⟨0, Γ₀, hyps, inst c.concl⟩
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let at' (m : String) (k : Deducer) : Deducer := stage s!"recognizerAt: {m}" k
    let hypOr := hypOrK K
    let lastHyp : Deducer := last hypOr
    let decidedNot : Deducer := dImpI L (lastFalse K)
    -- no name has an index in the empty scope
    let noScope : Deducer := dImpI L (lastFalse { K with more := ["indexOfNil"] })
    -- the primitives' names without an index among the names
    let primsAbsent (k : Deducer) : Deducer := (writerPrimNames P).foldr (fun (n, lem) k ↦
      decideIn K (fun Γ ↦ isSome (pc P "Reader.indexOf" [n, namesA Γ])) k
        (at' s!"{lem} a name" <|
          dRwHyp (evalRw K.G K.E [.delta (T.q + 4 + 2 * nFolds)] .head) hNames <|
          K.allEΓ (fun _ ↦ n) <| K.impE (K.solve 3) <|
          K.impE (K.cutThm lem (fun _ ↦ []) lastHyp) <| lastFalse K)) k
    let main : Deducer := dConjE L hStatic <| K.conjE <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
      let (iMarkers, iUniqs, iDec) := (Φ₂.length - 6, Φ₂.length - 4, Φ₂.length - 2)
      -- no marker's datatype is named as the trees' type
      let noTree : Deducer := dAllI L <| dImpI L <| fun Γ₃ Φ₃ ψ₃ ↦
        let (h, n) := (Φ₃.length - 1, Γ₃.length)
        (fun Γ Φ ψ ↦ dAllE L K.G K.E iMarkers (v (Γ.length - n)) (K.impE (K.byHyp h) <|
          K.conjE <| K.conjE <| fun Γ Φ ψ ↦ hypOr (Φ.length - 2) Γ Φ ψ) Γ Φ ψ) Γ₃ Φ₃ ψ₃
      (applyThm K "numOfKws" (fun Γ ↦ [numsA Γ])
          [hypOr hKws, hypOr iDec, hypOr hDigits] <| last fun iNumT ↦
        plainAtoms K T ((writerExcludedNames P).map (·.1)) numsA hKws
          (lemmas := writerExcludedNames P) <| primsAbsent <|
        applyThm K "recognizerDen" σ
          ([at' "a recognizer" (hypOr hRec), at' "no trees' marker" noTree,
            at' "the numerals" (hypOr iNumT)] ++
            writerPrims.flatMap (fun a ↦ [at' s!"{a} in no scope" noScope,
              at' s!"{a} no name" decidedNot]) ++
            writerAtoms.map (fun a ↦ at' s!"{a} plain" decidedNot) ++
            [at' "the constructors' labels" (hypOr iUniqs),
              at' "the datatype's index" (hypOr hIdx)]) lastHyp) Γ₂ Φ₂ ψ₂
    let _ := tysA
    let some d := main a.ctx a.hyps a.concl
      | dbgTrace "recognizerAt: not proved" fun _ ↦ none
    pure (a, d))

/-- The definitions' relation to the typing environment's holds by the names with a name after
them: a name with a type has its index among the names ({lit}`indexAppendOld`). In the context
of the name, the names, the environment and the relation's context. -/
def globSnoc (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("globSnoc", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let Γ := [treeTy, list treeTy, T.envTy, Defs3.ctxTy]
    let (nm, names, Ev, R) := (v 0, v 1, v 2, v 3)
    let single (x : Term) : Term := pc P "Prelude.single" [x]
    let a : Internal.Thm := ⟨0, Γ, [T.globT R Ev names],
      T.globT R Ev (pc P "Prelude.append" [names, single nm])⟩
    let unfold : List Internal.NormRule := [.delta (T.q + 2)]
    let eqHyp (h : ℕ) : Deducer := fun Γ Φ ψ ↦
      (dHyp Γ Φ ψ).orElse fun _ ↦ normHyps K [h] K.byNorm Γ Φ ψ
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (namesA, nmA, xA) := (at_ 2, at_ 3, at_ 4)
    let some d := (dRwBy (evalRw K.G K.E unfold .head) <|
        -- the relation unfolded, added after the hypothesis, of index 1
        dRwHyp (evalRw K.G K.E unfold .head) 0 <| dAllI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
      let hT := Φ₁.length - 1
      (fun Γ Φ ψ ↦ dAllE L K.G K.E 1 (xA Γ) (
        K.impE (stage "globSnoc: typed" (K.byHyp hT)) <| K.exE <| K.conjE <| fun Γ Φ ψ ↦
          let eqIdx := Φ.length - 2
          (K.exE <| K.conjE <| fun Γ Φ ψ ↦
            let (eqNth, convH) := (Φ.length - 2, Φ.length - 1)
            dExI L K.G K.E (at_ 5 Γ) (dConjI L
              (K.cutThm "indexAppendOld" (fun Γ ↦ [namesA Γ]) <| K.allEΓ xA <|
                K.allEΓ (fun Γ ↦ single (nmA Γ)) <|
                K.impE (stage "globSnoc: indexed" (normHyps K [eqIdx] (K.solve 3))) <|
                fun Γ Φ ψ ↦ normHyps K [eqIdx, Φ.length - 1]
                  (stage "globSnoc: the index" K.byNorm) Γ Φ ψ)
              (dExI L K.G K.E (at_ 6 Γ) (dConjI L
                (stage "globSnoc: the term" (eqHyp eqNth))
                (stage "globSnoc: the value" (K.byHyp convH))))) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
        Γ₁ Φ₁ ψ₁) a.ctx a.hyps a.concl
      | dbgTrace "globSnoc: not proved" fun _ ↦ none
    let _ := (nm, names, Ev, R)
    pure (a, d))

/-- That a body denotes a marker's datatype's recognizer, at states' parts: in the empty scope
and environment it denotes a function which at the quotation of every tree converges to the
quotation of a bit, true exactly where the tree is a member of the marker's datatype, as the
writer's recognizer does ({lit}`recognizerDen`). -/
def recDenT (P : Prog) (S : Defs) (R tys names nums ms m x : Term) : Term :=
  let o := P.o
  let nil := nilT treeTy
  let childT := (primT Kernel.Prim.child).getD Term.star
  let dd := apps childT [m, leafT (numeral 0)]
  -- beneath the function v0, the tree v1 and the value v2
  let agrees : Term := Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
    (Term.eq (v 1) (quoteV P (v 0)))
    (iffT o (truth o (v 0)) (truth o (pc P "Typing.memberOf" [sh 4 ms, sh 4 dd, v 2])))))
  let applied : Term := Internal.Logic.all o treeTy (Term.lam treeTy (S.conv
    (Term.lam nat (apps (Term.snd (S.levelN (Term.fst (sh 3 R)) (v 0)))
      [v 2, quoteV P (v 1)]))
    (Term.lam treeTy agrees)))
  Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
    (denT P S (sh 1 R) (sh 1 tys) (sh 1 names) (sh 1 nums) (sh 1 nil) (sh 1 nil) (sh 1 x)
      (v 0))
    applied))

/-- The hypotheses at the states are preserved by a marker to whose datatype's recognizer the
program's forms refer: the marker, before pending forms, leaves states whose reader has the
recognizer's name after the names and its resolved term after the terms, the recognizers'
environment now the typing's, whose datatypes are those of the recognizers' environment before
and the marker's. The recognizer the writer gives is the definition of the recognizer's atom as
a body, the variable of index 0, which denotes a function deciding membership; the recognizers'
insertion gives the definition ({name}`recAtMarker`), and the reader's step ({lit}`readDef`)
reads it, its name fresh. The definitions stay related to the environment's
({name}`globSnoc`); the recognizers of the datatypes before agree as before
({name}`recsExtend`), the name no recognizer's of theirs, and the marker's datatype's
recognizer, at the index of the names' length
({lit}`idxNew`, {lit}`nthLen`), decides membership by its denotation. In the context of the
body, the characters of the datatype's atom, the constructors' entries, the pending forms
after, the forms that remain, the states and the recognizers' environment. -/
def markerReadAt (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("markerReadAt", fun ix E ↦ do
    let K : Kit := ⟨markerProg P, S, E, ix, ["eraseMarker", "recAtMarker"] ++ lookupEqNames⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let nil := nilT treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"markerReadAt @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "markerReadAt: no partition" fun _ ↦ none
    let atom (cs : Term) : Term := nodeT (Term.pair (numeral 1) cs)
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let app (xs ys : Term) : Term := pc P "Prelude.append" [xs, ys]
    let one (x : Term) : Term := pc P "Prelude.single" [x]
    let noms (e : Term) : Term := pc P "Typing.envNoms" [e]
    -- the recognizer's atom, of the datatype's atom's characters, and a body's resolution
    let recAtom (cs : Term) : Term := pc P "Datatype.memberName" [atom cs]
    let resolved (s : Passes) (x : Term) : Term := pc P "Reader.resolve" [s.tys, s.names,
      pc P "Reader.expandNums" [s.nums, x], nil]
    let m := markerT (atom (v 1)) (v 2)
    let s : Passes := { passesAt 5 (v 4) with
      ws := some (consT treeTy m (v 3)), recEnv := some (v 14) }
    let Γ₀ := [treeTy, Ls, Ls, Ls, Ls] ++ passesCtx T ++ [T.envTy]
    let nmR := pc P "Reader.nameOf" [recAtom (v 1)]
    let s' : Passes := { s with
      names := app s.names (one nmR)
      terms := app s.terms (one (get (resolved s (v 0))))
      ws := some (v 3), recEnv := none }
    let dn := pc P "Typing.atomName" [atom (v 1)]
    let hyps := s.hyps P S T X₀ ++ [Term.eq (noms s.env) (namesSnoc P (noms (v 14)) dn),
      truth o (occInT P (memberAtomT P dn) s.fs), userNameT P nmR,
      Term.eq (get (pc P "Recognize.recognizer" [s.ms, m])) (defForm P (recAtom (v 1)) (v 0)),
      recDenT P S (s.rel P) s.tys s.names s.nums s.ms m (v 0)]
    let a : Internal.Thm := ⟨0, Γ₀, hyps, conjAll o (s'.hyps P S T X₀ ++
      [Internal.Logic.imp o (s'.concl P T X₀) (s.concl P T X₀)])⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (XA, csA, xsA, wsA, esA, fsA, msA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5, at_ 6)
    let (termsA, namesA, numsA, tysA, EA, ErA) :=
      (at_ 7, at_ 8, at_ 9, at_ 10, at_ 12, at_ 14)
    let dA (Γ : List Tree) : Term := atom (csA Γ)
    let mA (Γ : List Tree) : Term := markerT (dA Γ) (xsA Γ)
    let dnA (Γ : List Tree) : Term := pc P "Typing.atomName" [dA Γ]
    let nA (Γ : List Tree) : Term := recAtom (csA Γ)
    let nmA (Γ : List Tree) : Term := pc P "Reader.nameOf" [nA Γ]
    let sA (Γ : List Tree) : Passes := { passesAt (5 + (Γ.length - Γ₀.length)) (esA Γ) with
      ws := some (consT treeTy (mA Γ) (wsA Γ)), recEnv := some (ErA Γ) }
    let restA (Γ : List Tree) : Passes := { sA Γ with ws := some (wsA Γ) }
    let tA (Γ : List Tree) : Term := get (resolved (sA Γ) (XA Γ))
    let names'A (Γ : List Tree) : Term := app (namesA Γ) (one (nmA Γ))
    let terms'A (Γ : List Tree) : Term := app (termsA Γ) (one (tA Γ))
    let stA (Γ : List Tree) : Term := progState (tysA Γ) (numsA Γ) (namesA Γ) (termsA Γ)
    let kA (Γ : List Tree) : Term := defForm P (nA Γ) (XA Γ)
    let rsA (Γ : List Tree) : Term := flatT P (Term.snd ((restA Γ).inserted P))
    let recA (Γ : List Tree) : Term := pc P "Recognize.recognizer" [msA Γ, mA Γ]
    let referred (Γ : List Tree) : Term := occInT P (memberAtomT P (dnA Γ)) (fsA Γ)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    -- the hypotheses' indices
    let (hX, hC, hO, hR, hK, hRej, hGlob, hNums, hNames, hKws, hLen, hRecs) :=
      (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)
    let (hP, hOcc, hIns, hUsed, hUser, hSorts, hAl, hAlKw, hAlTys, hMs, hMk, hStatic) :=
      (12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23)
    let (hNoms, hRef, hUserR, hDef, hDen) := (24, 25, 26, 27, 28)
    let recsIdx := T.q + 6 + 2 * nFolds
    -- at a datatype of the environment, the variable of the context of {lit}`n` variables,
    -- under the hypothesis of index {lit}`hHas`: one of the recognizers' environment's, by
    -- {lit}`old`, or the marker's, by {lit}`new` under the datatype's equation with it
    let cases (n hHas : ℕ) (old new : Deducer) : Deducer :=
      let dv (Γ : List Tree) : Term := v (Γ.length - n)
      decideIn K (fun Γ ↦ hasT P (dv Γ) (noms (ErA Γ)))
        (K.cutThm "hasSnocCases" (fun Γ ↦ [noms (ErA Γ)]) <| K.allEΓ dv <| K.allEΓ dnA <|
          K.impE (at' "a datatype after the marker's"
            (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ hHas) .full) hHas
              (K.norm dHyp) Γ Φ ψ)) <|
          K.impE (dImpI L (lastFalse K)) <| last fun iEq ↦
          K.cutThm "equalSymm" (fun Γ ↦ [dv Γ, dnA Γ]) <| K.impE (K.byHyp iEq) <|
          last fun iEq' ↦ K.cutThm "equalSound" (fun Γ ↦ [dv Γ]) <| K.allEΓ dnA <|
          K.impE (K.byHyp iEq') <| normLastK K new)
        old
    -- the hypotheses at the states the steps leave
    let apply (iO iOccRest iMkRest nP wP st iApp iUnres iNotIdx iNth : ℕ) : Deducer :=
      at' "the states after" <|
      -- the name is no recognizer's of a datatype of the environment before: one the forms
      -- refer to is among the names, of which the name is none
      let notRec : Deducer := dAllI L <| dImpI L <| dImpI L <| fun Γ₈ Φ₈ ψ₈ ↦
        let (hHas, hEq, n₈) := (Φ₈.length - 2, Φ₈.length - 1, Γ₈.length)
        let named := evalRw K.G K.E [.hyp hEq] .full
        (fun Γ Φ ψ ↦ dAllE L K.G K.E hIns (v (Γ.length - n₈)) (
          K.impE (stage "markerReadAt: a datatype" (hypOr hHas)) <|
          K.impE (stage "markerReadAt: the recognizer referred to"
            (dRwBy named (K.byHyp hRef))) <|
          last fun iIdx ↦ dRwHyp named iIdx <| last fun iIdx' ↦ dImpE L iNotIdx
            (stage "markerReadAt: the recognizer indexed" (K.byHyp iIdx'))
            (dFalse L dHyp)) Γ Φ ψ) Γ₈ Φ₈ ψ₈
      -- the new name's index among the names with it after them
      let newIdx : Deducer := K.cutThm "idxNew" (fun Γ ↦ [namesA Γ]) <| K.allEΓ nmA <|
        K.impE (hypOr iNotIdx) <| byLast K
      let recs : Deducer :=
        applyThm K "recsExtend" (fun Γ ↦ [nmA Γ, namesA Γ, ErA Γ, ErA Γ, (sA Γ).rel P])
          [stage "markerReadAt: the recognizers before" (hypOr hRecs),
            stage "markerReadAt: the datatypes" K.byNorm,
            stage "markerReadAt: no recognizer's name" notRec] <| last fun iRecs₁ ↦
        dRwBy (evalRw K.G K.E [.delta recsIdx] .head) <|
        dAllI L <| dImpI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
        let (hHas, hIdx, n) := (Φ₁.length - 2, Φ₁.length - 1, Γ₁.length)
        cases n hHas
          (at' "a datatype before" <|
            dRwHyp (evalRw K.G K.E [.delta recsIdx] .head) iRecs₁ <|
            K.allEΓ (fun Γ ↦ v (Γ.length - n)) <| K.impE (K.solve 3) <|
            K.impE (K.byHyp hIdx) <| last K.byHyp)
          (at' "the marker's datatype" fun Γ Φ ψ ↦
            dExI L K.G K.E (pc P "Prelude.length" [namesA Γ]) (dConjI L
              (stage "markerReadAt: the recognizer's index" newIdx)
              (dExI L K.G K.E (tA Γ) (dConjI L
                (stage "markerReadAt: the recognizer's term"
                  (normHyps K [hLen, iNth] K.byNorm))
                (stage "markerReadAt: the recognizer's value" fun Γ' Φ' ψ' ↦
                  dConv L K.G K.E S (atPos nP Γ') (atPos wP Γ')
                    (stage "markerReadAt: stable" (instNK K st (fun _ ↦ v 0) K.byNorm))
                    (stage "markerReadAt: decides membership" (K.byHyp iApp)) Γ' Φ' ψ'))))
            Γ Φ ψ) Γ₁ Φ₁ ψ₁
      let ins : Deducer :=
        applyThm K "insExtend" (fun Γ ↦ [nmA Γ, namesA Γ, ErA Γ, ErA Γ, fsA Γ])
          [stage "markerReadAt: referred to before" (hypOr hIns),
            stage "markerReadAt: the datatypes" K.byNorm] <| last fun iIns₁ ↦
        dAllI L <| dImpI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
        let (hHas, hRefD, n) := (Φ₁.length - 2, Φ₁.length - 1, Γ₁.length)
        cases n hHas
          (at' "a recognizer referred to before" fun Γ Φ ψ ↦
            dAllE L K.G K.E iIns₁ (v (Γ.length - n)) (K.impE (K.solve 3) <|
              K.impE (K.byHyp hRefD) <| last K.byHyp) Γ Φ ψ)
          (at' "the marker's recognizer among the names" newIdx) Γ₁ Φ₁ ψ₁
      conjIs L
        [stage "markerReadAt: the rest expands" (K.byHyp hX),
          stage "markerReadAt: the rest checks" (K.byHyp hC),
          stage "markerReadAt: the rest's recognizers" (hypOr iO),
          stage "markerReadAt: the rest reads" (K.byHyp hR),
          stage "markerReadAt: the kernel checks" (K.byHyp hK),
          stage "markerReadAt: no rejection" (hypOr hRej),
          stage "markerReadAt: related" (applyThm K "globSnoc"
            (fun Γ ↦ [nmA Γ, namesA Γ, EA Γ, (sA Γ).rel P]) [hypOr hGlob] (last K.byHyp)),
          stage "markerReadAt: the numerals" (hypOr hNums),
          stage "markerReadAt: the names" (applyThm K "namesExtend"
            (fun Γ ↦ [nmA Γ, namesA Γ]) [hypOr hNames, hypOr iUnres] (last K.byHyp)),
          stage "markerReadAt: the keywords" (hypOr hKws),
          stage "markerReadAt: the lengths" (
            K.cutThm "lenSnoc" (fun Γ ↦ [namesA Γ]) <| K.allEΓ nmA <|
            K.cutThm "lenSnoc" (fun Γ ↦ [termsA Γ]) <| K.allEΓ tA <| fun Γ Φ ψ ↦
            normHyps K [hLen, Φ.length - 3, Φ.length - 1] K.byNorm Γ Φ ψ),
          stage "markerReadAt: the recognizers" recs,
          stage "markerReadAt: the bodies" (K.byHyp hP),
          stage "markerReadAt: the occurrences after" (hypOr iOccRest),
          stage "markerReadAt: the recognizers referred to" ins,
          stage "markerReadAt: the names' occurrences" (
            K.cutThm "allSnoc" (fun Γ ↦ [namesA Γ]) <|
            K.allEΓ (fun Γ ↦ usedPred P (fsA Γ)) <| K.allEΓ nmA <|
            K.impE (hypOr hUsed) <| K.impE (K.byHyp hRef) <| last K.byHyp),
          stage "markerReadAt: the names' origin" (
            K.cutThm "allSnoc" (fun Γ ↦ [namesA Γ]) <|
            K.allEΓ (fun _ ↦ userPred P) <| K.allEΓ nmA <|
            K.impE (hypOr hUser) <| K.impE (K.byHyp hUserR) <| last K.byHyp),
          stage "markerReadAt: no sort" (hypOr hSorts),
          stage "markerReadAt: the aliases" (hypOr hAl),
          stage "markerReadAt: the aliases of types read first" (hypOr hAlKw),
          stage "markerReadAt: the aliases abbreviated" (hypOr hAlTys),
          stage "markerReadAt: the markers" (hypOr hMs),
          stage "markerReadAt: the markers that remain" (hypOr iMkRest),
          stage "markerReadAt: the markers and the numerals" (hypOr hStatic),
          stage "markerReadAt: the conclusion" (dImpI L (last K.byHyp))]
    -- the terms the reader ends with: the terms, the term read, and further ones
    let finals (iO iOccRest iMkRest nP wP st iApp iUnres iNotIdx : ℕ) : Deducer :=
      at' "the final terms" <|
      K.cutThm "readExt" (fun Γ ↦ [rsA Γ]) <| K.allEΓ (fun Γ ↦ progState (tysA Γ) (numsA Γ)
        (names'A Γ) (terms'A Γ)) <| K.exE <| fun Γ₇ Φ₇ ψ₇ ↦
      let n₇ := Γ₇.length
      let extA (Γ : List Tree) : Term := v (Γ.length - n₇)
      let iExt := Φ₇.length - 1
      (K.cutThm "appendSnoc" (fun Γ ↦ [termsA Γ, tA Γ, extA Γ]) <| last fun iSnoc ↦
        normHyps K [iExt, iSnoc] <|
        K.cutThm "nthLen" (fun Γ ↦ [termsA Γ]) <| K.allEΓ tA <| K.allEΓ extA <|
        last fun iNth ↦ apply iO iOccRest iMkRest nP wP st iApp iUnres iNotIdx iNth)
        Γ₇ Φ₇ ψ₇
    -- the reader's step
    let reader (iO iOccRest iMkRest nP wP st iApp : ℕ) : Deducer := at' "the reader" <|
      applyThm K "readPrefix" (fun Γ ↦ [rsA Γ, pc P "Reader.progStep" [stA Γ, kA Γ]])
        [stage "markerReadAt: the reader's run" (K.byHyp hR)] <|
      applyThm K "readDef" (fun Γ ↦ [XA Γ, nA Γ, termsA Γ, namesA Γ, numsA Γ, tysA Γ])
        [stage "markerReadAt: the reader's step" (lastOr K)] <|
      K.conjE <| K.conjE <| K.conjE <| fun Γ₅ Φ₅ ψ₅ ↦
        let (iFresh, iRead) := (Φ₅.length - 4, Φ₅.length - 1)
        (normHyps K [iRead] <|
          applyThm K "freshParts" (fun Γ ↦ [nmA Γ, namesA Γ, numsA Γ, tysA Γ])
            [stage "markerReadAt: fresh" (hypOr iFresh)] <| K.conjE <| K.conjE <| fun Γ Φ ψ ↦
          finals iO iOccRest iMkRest nP wP st iApp (Φ.length - 4) (Φ.length - 2) Γ Φ ψ)
          Γ₅ Φ₅ ψ₅
    let some d := (normHyps K [hNoms, hDef] <|
        decideIn K referred (at' "not referred to" (K.hypFalse hRef)) <|
        decideOpt K recA (at' "no recognizer" (K.hypFalse hO)) <|
        applyThm K "someTruth" (fun Γ ↦ [Term.fst ((restA Γ).inserted P)])
          [stage "markerReadAt: the recognizers' insertion" (K.byHyp hO)] <| last fun iO ↦
        normHyps K [hOcc] <| K.conjE <| last fun iOccRest ↦
        normHyps K [hMk] <| K.conjE <| last fun iMkRest ↦
        -- the body's denotation: its resolved term, the threshold and the value
        dExE L K.G K.E hDen <| K.conjE <| fun Γ₈ Φ₈ ψ₈ ↦
        let (iDen, iApp) := (Φ₈.length - 2, Φ₈.length - 1)
        denE K iDen (fun _ nP wP st ↦ reader iO iOccRest iMkRest nP wP st iApp) Γ₈ Φ₈ ψ₈)
        a.ctx a.hyps a.concl
      | dbgTrace "markerReadAt: not proved" fun _ ↦ none
    pure (a, d))

/-- The fold of a datatype's declaration over a list of its constructors, of the datatype's name
and the number of all its constructors: the number of the list's constructors, whether each is
well formed, their declarations and their definitions, each constructor read at its position,
the number of all the constructors less one and the number of those after it. -/
def ctorsFold (P : Prog) (d nc cs : Term) : Term :=
  let Ls := list treeTy
  let R := prod treeTy (prod treeTy (prod Ls Ls))
  let addT := (primT Kernel.Prim.add).getD Term.star
  let subT := (primT Kernel.Prim.sub).getD Term.star
  let acc := v 0
  let x := pc P "Datatype.ctorDecl" [sh 2 d,
    apps subT [apps subT [sh 2 nc, leafT (numeral 1)], Term.fst acc], v 1]
  foldrT treeTy R (Term.lam treeTy (Term.lam R (Term.pair
      (apps addT [Term.fst acc, leafT (numeral 1)])
      (Term.pair (pc P "Prelude.and" [Term.fst x, Term.fst (Term.snd acc)])
        (Term.pair (consT treeTy (Term.fst (Term.snd x)) (Term.fst (Term.snd (Term.snd acc))))
          (consT treeTy (Term.snd (Term.snd x)) (Term.snd (Term.snd (Term.snd acc)))))))))
    (Term.pair (leafT bnilT) (Term.pair (leafT (numeral 1))
      (Term.pair (nilT treeTy) (nilT treeTy)))) cs

/-- The declarations of the constructors of a list ({name}`ctorsFold`). -/
def ctorDeclsT (P : Prog) (d nc cs : Term) : Term :=
  Term.fst (Term.snd (Term.snd (ctorsFold P d nc cs)))

/-- The definitions of the constructors of a list ({name}`ctorsFold`). -/
def ctorDefsT (P : Prog) (d nc cs : Term) : Term :=
  Term.snd (Term.snd (Term.snd (ctorsFold P d nc cs)))

/-- The reading of a datatype's declaration, a list of a head, the datatype's atom and its
constructors: whether the constructors are well formed and the atom is one, the datatype's
declaration before the constructors' ({name}`ctorDeclsT`), and the abbreviation of the atom as
the trees' type before the constructors' definitions ({name}`ctorDefsT`). The constructors'
reading is kept folded. In the context of the constructors, the atom and the head. -/
def dataDeclAt (P : Prog) (S : Defs) : Step :=
  ("dataDeclAt", fun ix E ↦ do
    let K : Kit := ⟨{ P with folded := P.folded ++ ["Datatype.ctorDecl"] }, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [Ls, treeTy, treeTy]
    let (cs, dA, h) := (v 0, v 1, v 2)
    let e := nodeT (Term.pair (numeral 2) (consT treeTy h (consT treeTy dA cs)))
    let d := pc P "Datatype.atomName" [dA]
    let nc := pc P "Datatype/Txs.length" [cs]
    let r := ctorsFold P d nc cs
    let a : Internal.Thm := ⟨0, Γ, [], Term.eq (pc P "Datatype.dataDecl" [e])
      (Term.pair (pc P "Prelude.and" [Term.fst (Term.snd r), pc P "Datatype.isAtomTx" [dA]])
        (Term.pair (consT treeTy (pc P "Datatype.dataD" [d]) (ctorDeclsT P d nc cs))
          (consT treeTy (pc P "Datatype.sx3" [pc P "Datatype.aDeftype" [], dA,
            pc P "Datatype.aT" []]) (ctorDefsT P d nc cs))))⟩
    let some d := byNormTraced K "dataDeclAt" a.ctx a.hyps a.concl
      | dbgTrace "dataDeclAt: not proved" fun _ ↦ none
    pure (a, d))

/-- The declarations of constructors hold no alias: at each name, the expansion's alias among
them is that among none. By induction on the constructors, a constructor's declaration no
alias's. In the context of the constructors, under the datatype's name, the number of all the
constructors and the name. -/
def declsNoAlias (P : Prog) (S : Defs) : Step :=
  ("declsNoAlias", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let fa (n dv : Term) : Term := pc P "Datatype.findAlias" [n, dv]
    -- under the quantifiers: the name v0, the number v1, the datatype's name v2, the list v3
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.all o treeTy
      (Term.lam treeTy (Internal.Logic.all o treeTy (Term.lam treeTy
        (Term.eq (fa (v 0) (ctorDeclsT P (v 2) (v 1) (v 3))) (fa (v 0) (nilT treeTy))))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let intro (k : Deducer) : Deducer := dAllI L <| dAllI L <| dAllI L k
    let base : Deducer := intro (byNormTraced K "declsNoAlias: none")
    -- a construction: the head v(0), the tail v(1), the datatype's name v(2), the number
    -- v(3), the name v(4)
    let step : Deducer := intro fun Γ Φ ψ ↦
      dAllE L K.G K.E 0 (at_ 2 Γ) (K.allEΓ (at_ 3) <| K.allEΓ (at_ 4) <| normLastK K <|
        byNormTraced K "declsNoAlias: a constructor") Γ Φ ψ
    listInduction "declsNoAlias" φ base step)

/-- The expansion's alias of a name among declarations with others after them that hold no
alias of it is its alias among the declarations: by induction on the declarations. In the
context of the declarations, under the others and the name. -/
def findAliasAppend (P : Prog) (S : Defs) : Step :=
  ("findAliasAppend", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let fa (n dv : Term) : Term := pc P "Datatype.findAlias" [n, dv]
    let app (xs ys : Term) : Term := pc P "Datatype/Decls.append" [xs, ys]
    -- under the quantifiers: the name v0, the others v1, the declarations v2
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o treeTy (Term.lam treeTy
      (Internal.Logic.imp o (Term.eq (fa (v 0) (v 1)) (fa (v 0) (nilT treeTy)))
        (Term.eq (fa (v 0) (app (v 2) (v 1))) (fa (v 0) (v 2)))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let intro (k : Deducer) : Deducer := dAllI L <| dAllI L <| dImpI L k
    let base : Deducer := intro <| normLastK K <| byNormTraced K "findAliasAppend: none"
    -- a construction: the head v(0), the tail v(1), the others v(2), the name v(3)
    let step : Deducer := intro <| last fun hNo ↦ fun Γ Φ ψ ↦
      dAllE L K.G K.E 0 (at_ 2 Γ) (K.allEΓ (at_ 3) <|
        K.impE (fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦ eqByHyp K hNo Γ Φ ψ) <| normLastK K <|
        byNormTraced K "findAliasAppend: a declaration") Γ Φ ψ
    listInduction "findAliasAppend" φ base step)

/-- The aliases' coherence passes between declarations with the same aliases: where each name's
alias among the first is its alias among the second, the first are coherent with the typing
environment's abbreviations, hold no alias of a type read first and have their aliases
abbreviated ({name}`aliasT`, {name}`aliasKwT`, {name}`aliasTysT`) where the second are. The
aliases' equation is stated from the first to the second, or, where {lit}`back` holds, from
the second to the first. In the context of the first, the second, the typing environment, the
markers and the type abbreviations. -/
def aliasSame (P : Prog) (S : Defs) (T : Defs3) (back : Bool) : Step :=
  (if back then "aliasSameBack" else "aliasSame", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let Γ₀ := [Ls, Ls, T.envTy, Ls, Ls]
    let (dvA, dvB, Ev, ms, tys) := (v 0, v 1, v 2, v 3, v 4)
    let fa (n dv : Term) : Term := pc P "Datatype.findAlias" [n, dv]
    let same := Internal.Logic.all o treeTy (Term.lam treeTy (if back
      then Term.eq (fa (v 0) (sh 1 dvB)) (fa (v 0) (sh 1 dvA))
      else Term.eq (fa (v 0) (sh 1 dvA)) (fa (v 0) (sh 1 dvB))))
    let a : Internal.Thm := ⟨0, Γ₀,
      [same, aliasT P dvB Ev ms, aliasKwT P dvB, aliasTysT P dvB tys],
      conjAll o [aliasT P dvA Ev ms, aliasKwT P dvA, aliasTysT P dvA tys]⟩
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    -- the aliases' equation at a name, a rule, then the hypothesis at the name
    let atName (h : ℕ) : Deducer := dAllI L fun Γ₁ Φ₁ ψ₁ ↦
      let n := Γ₁.length
      (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (v (Γ.length - n)) (normLastK K fun Γ Φ ψ ↦
        dAllE L K.G K.E h (v (Γ.length - n)) (last K.byHyp) Γ Φ ψ) Γ Φ ψ) Γ₁ Φ₁ ψ₁
    let kw (name : String) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dAllE L K.G K.E 0 (pc P name []) (normLastK K k) Γ Φ ψ
    let some d := conjIs L [stage "aliasSame: coherent" (atName 1),
        stage "aliasSame: the types read first"
          (kw "Reader.kwT" <| kw "Reader.kwUnit" <| K.byHyp 2),
        stage "aliasSame: abbreviated" (atName 3)] a.ctx a.hyps a.concl
      | dbgTrace "aliasSame: not proved" fun _ ↦ none
    pure (a, d))

/-- The typing reads a datatype's atom as the datatype, where the atom is named as neither type
the typing reads first, its name has no abbreviation in the environment and is among the
environment's datatypes' names: the typing's tests at an atom decided in its order. In the
context of the atom's characters and the typing environment. -/
def dataRead (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("dataRead", fun ix E ↦ do
    let K : Kit := ⟨aliasProg P, S, E, ix,
      lookupEqNames ++ ["hasNameNil", "rawAtomEq", "rtFst", "rtKids", "eaFst", "eaKids"]⟩
    let L := K.L
    let o := P.o
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let Γ₀ := [list treeTy, T.envTy]
    let atom (cs : Term) : Term := nodeT (Term.pair (numeral 1) cs)
    let named (cs : Term) (kw : String) : Term := pc P "Reader.named" [atom cs, pc P kw []]
    let abbr (cs Ev : Term) : Term :=
      pc P "Typing.lookupName" [atomNameT (atom cs), pc P "Typing.envAl" [Ev]]
    let has (cs Ev : Term) : Term :=
      pc P "Typing.hasName" [atomNameT (atom cs), pc P "Typing.envNoms" [Ev]]
    let (cs, Ev) := (v 0, v 1)
    let a : Internal.Thm := ⟨0, Γ₀,
      [notTest o (named cs "Reader.kwT"), notTest o (named cs "Reader.kwUnit"),
        notTest o (isSome (abbr cs Ev)), truth o (has cs Ev)],
      Term.eq (get (pc P "Typing.readTy" [Ev, rawT T Ev (atom cs)]))
        (pc P "Typing.tyData" [atomNameT (atom cs)])⟩
    let (EA, csA) := (atPos 0, atPos 1)
    let refuted (h : ℕ) : Deducer := dImpE L h (K.solve 3) (dFalse L dHyp)
    let some d := (decideIn K (fun Γ ↦ named (csA Γ) "Reader.kwT")
        (decideIn K (fun Γ ↦ named (csA Γ) "Reader.kwUnit")
          (decideOpt K (fun Γ ↦ abbr (csA Γ) (EA Γ))
            (decideIn K (fun Γ ↦ has (csA Γ) (EA Γ))
              (stage "dataRead: no datatype" (K.hypFalse 3))
              (stage "dataRead: a datatype's name" (byNormTraced K "dataRead")))
            (stage "dataRead: an abbreviation" (refuted 2)))
          (stage "dataRead: the unit type" (refuted 1)))
        (stage "dataRead: the trees' type" (refuted 0))) a.ctx a.hyps a.concl
      | dbgTrace "dataRead: not proved" fun _ ↦ none
    pure (a, d))

/-- A predicate of each kernel form of typed forms after others holds of each kernel form of
the typed forms: by induction on the others; at a construction the head's kernel form is none,
a template's instance's, or one of which the predicate holds. In the context of the others,
under the typed forms and the predicate. -/
def kernelAfter (P : Prog) (S : Defs) : Step :=
  ("kernelAfter", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let Pr := exp treeTy omega
    let kf (ts : Term) : Term := pc P "Datatype.kernelForms" [ts]
    -- under the quantifiers: the predicate v0, the typed forms v1, the others v2
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o Pr (Term.lam Pr
      (Internal.Logic.imp o (S.allL (v 0) (kf (txsApp P (v 2) (v 1))))
        (S.allL (v 0) (kf (v 1)))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let intro (k : Deducer) : Deducer := dAllI L <| dAllI L <| dImpI L k
    let base : Deducer := intro (last K.byHyp)
    -- a construction: the head v(0), the tail v(1), the typed forms v(2), the predicate v(3)
    let step : Deducer := intro <| last fun hAll ↦ fun Γ₁ Φ₁ ψ₁ ↦
      let (b, tl, ys, pr) := (at_ 0, at_ 1, at_ 2, at_ 3)
      -- the induction hypothesis at the predicate's holding of the rest's kernel forms
      let rest (h : ℕ) : Deducer := fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (ys Γ) (K.allEΓ pr <| K.impE (K.byHyp h) <| last K.byHyp) Γ Φ ψ
      let close : Deducer := fun Γ Φ ψ ↦
        (rest hAll Γ Φ ψ).orElse fun _ ↦
          (normHyps K [hAll] <| K.conjE <| last rest) Γ Φ ψ
      (K.treeNode (b Γ₁) fun Γ₂ Φ₂ ψ₂ ↦
        splitCond K Γ₁.length (kf (consT treeTy (b Γ₁) (txsApp P (tl Γ₁) (ys Γ₁)))) 12
          (stage "kernelAfter: a form" close) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    listInduction "kernelAfter" φ base step)

/-- Whether a test, a function of a tree, holds of an element of a list, by the prelude's right
fold of the disjunction. -/
def anyOfT (P : Prog) (f xs : Term) : Term :=
  foldrT treeTy treeTy (Term.lam treeTy (Term.lam treeTy
    (pc P "Prelude.or" [Term.app (sh 2 f) (v 1), v 0]))) (leafT bnilT) xs

/-- A test that holds of a tree holds of an element of a list with the tree after trees and
before others: by induction on the trees before it. In the context of those trees, under the
others, the tree and the test. -/
def anyAt (P : Prog) (S : Defs) : Step :=
  ("anyAt", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let Fn := exp treeTy treeTy
    let all (A : Tree) (b : Term) : Term := Internal.Logic.all o A (Term.lam A b)
    let app (xs ys : Term) : Term := pc P "Prelude.append" [xs, ys]
    -- under the quantifiers: the test v0, the tree v1, the others v2, the trees before v3
    let φ := all Ls (all treeTy (all Fn (Internal.Logic.imp o (truth o (Term.app (v 0) (v 1)))
      (truth o (anyOfT P (v 0) (app (v 3) (consT treeTy (v 1) (v 2))))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let intro (k : ℕ → Deducer) : Deducer := dAllI L <| dAllI L <| dAllI L <| dImpI L
      fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let base : Deducer := intro fun h ↦
      decideIn K (fun Γ ↦ Term.app (at_ 2 Γ) (at_ 1 Γ)) (K.hypFalse h) (K.solve 3)
    -- a construction: the head v(0), the tail v(1), the others v(2), the tree v(3), the test
    -- v(4)
    let step : Deducer := intro fun h ↦
      decideIn K (fun Γ ↦ Term.app (at_ 4 Γ) (at_ 0 Γ))
        (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (at_ 2 Γ) (K.allEΓ (at_ 3) <| K.allEΓ (at_ 4) <|
          K.impE (K.byHyp h) <| fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
        (K.solve 3)
    listInduction "anyAt" φ base step)

/-- The entries a marker holds of declarations: the marker's children after the datatype's
atom, each constructor's declaration's entry. -/
def entriesT (P : Prog) (dv dA ds : Term) : Term :=
  call D.tail [treeTy] [call D.children [] [pc P "Datatype.marker" [dv, dA, ds]]]

/-- The representation of no variable field's type, as a marker's entry holds it: the empty
form, the declarations' aliases expanded. -/
def noRestT (P : Prog) (dv : Term) : Term :=
  pc P "Datatype.expandAliases" [dv, pc P "Typing.tx0" []]

/-- The entry a marker holds of a constructor without a variable field: its position, its field
types' representations, the test of a variable field, which does not hold, and the
representation of no type. -/
def entryT (P : Prog) (dv j fs : Term) : Term :=
  node0 (consT treeTy j (consT treeTy (node0 (repsT P dv fs))
    (consT treeTy (varFlagT P fs) (consT treeTy (noRestT P dv) (nilT treeTy)))))

/-- The entries a marker holds of the declaration of a constructor without a variable field
before others: the constructor's entry ({name}`entryT`) before the others' entries. The
constructor's tests of a variable field decided. In the context of the fields' types, the
constructor's atom, its position, the datatype's name, the declarations, the datatype's atom
and the other declarations. -/
def ctorEntry (P : Prog) (S : Defs) : Step :=
  ("ctorEntry", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [Ls, treeTy, treeTy, treeTy, Ls, treeTy, Ls]
    let (fs, nm, j, d, dv, dA, rest) := (v 0, v 1, v 2, v 3, v 4, v 5, v 6)
    let ltT ← primT Kernel.Prim.lt
    let subT ← primT Kernel.Prim.sub
    let c := nodeT (Term.pair (numeral 2) (consT treeTy nm fs))
    let nr := pc P "Datatype/Txs.length" [fs]
    let more := apps ltT [leafT (numeral 1), nr]
    let amp := pc P "Datatype.namedTx"
      [pc P "Datatype.nthTx" [fs, apps subT [nr, leafT (numeral 2)]], pc P "Datatype.kwAmp" []]
    let decl := pc P "Datatype.ctorDecl" [d, j, c]
    let a : Internal.Thm := ⟨0, Γ, [notTest P.o (pc P "Prelude.and" [more, amp])],
      Term.eq (entriesT P dv dA (consT treeTy (Term.fst (Term.snd decl)) rest))
        (consT treeTy (entryT P dv j fs) (entriesT P dv dA rest))⟩
    let at_ (t : Term) (Γ' : List Tree) : Term := sh (Γ'.length - Γ.length) t
    let written := byNormTraced K "ctorEntry"
    let some d := decideIn K (at_ more) written
        (decideIn K (at_ amp) written (refuteNot K 0)) a.ctx a.hyps a.concl
      | dbgTrace "ctorEntry: not proved" fun _ ↦ none
    pure (a, d))

/-- The facts of a datatype's block that the steps at its forms preserve, at states: the typing
environment's datatypes are those of the recognizers' environment and the datatype, whose name
has no abbreviation in the environment and is among its datatypes' names. Of the characters of
the datatype's atom. -/
def blockFacts (P : Prog) (s : Passes) (Er csd : Term) : List Term :=
  let o := P.o
  let Da := nodeT (Term.pair (numeral 1) csd)
  let noms (e : Term) : Term := pc P "Typing.envNoms" [e]
  [Term.eq (noms s.env) (namesSnoc P (noms Er) (pc P "Typing.atomName" [Da])),
    notTest o (pc P "Prelude.isSome"
      [pc P "Typing.lookupName" [atomNameT Da, pc P "Typing.envAl" [s.env]]]),
    truth o (pc P "Typing.hasName" [atomNameT Da, noms s.env])]

/-- The facts of a datatype's block that read the states' declarations and markers, which the
steps at the block's forms leave as they are: each name's alias among the declarations is its
alias among those before the block, and the typing reads the datatype's constructors off the
markers as the marker's entries. Of the characters of the datatype's atom, the declarations
before the block and the marker's entries. -/
def blockStatics (P : Prog) (s : Passes) (csd dv₀ xs : Term) : List Term :=
  let fa (n dv : Term) : Term := pc P "Datatype.findAlias" [n, dv]
  [Internal.Logic.all P.o treeTy (Term.lam treeTy
      (Term.eq (fa (v 0) (sh 1 s.dv)) (fa (v 0) (sh 1 dv₀)))),
    Term.eq (pc P "Typing.markerCtors" [s.ms, nodeT (Term.pair (numeral 1) csd)])
      (Term.pair (leafT (numeral 1)) xs)]

/-- The soundness at the forms that remain after a datatype's block, at the block's marker, to
whose datatype's recognizer the program's forms refer, the recognizer the writer gives the
definition of the recognizer's atom as a body, the variable of index 0, which denotes a
function deciding membership: the marker leaves states of which the hypotheses hold again
({name}`markerReadAt`), at which the hypothesis on the forms after gives the conclusion. In the
context of the body, the characters of the datatype's atom, the constructors' entries, the
forms that remain, the states and the recognizers' environment. -/
def blockEndAt (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("blockEndAt", fun ix E ↦ do
    let K : Kit := ⟨markerProg P, S, E, ix, ["eraseMarker", "recAtMarker"] ++ lookupEqNames⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let nil := nilT treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"blockEndAt @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "blockEndAt: no partition" fun _ ↦ none
    let atom (cs : Term) : Term := nodeT (Term.pair (numeral 1) cs)
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let app (xs ys : Term) : Term := pc P "Prelude.append" [xs, ys]
    let one (x : Term) : Term := pc P "Prelude.single" [x]
    let recAtom (cs : Term) : Term := pc P "Datatype.memberName" [atom cs]
    let m := markerT (atom (v 1)) (v 2)
    let s : Passes := { passesAt 4 (v 3) with
      ws := some (consT treeTy m nil), recEnv := some (v 13) }
    let Γ₀ := [treeTy, Ls, Ls, Ls] ++ passesCtx T ++ [T.envTy]
    let nmR := pc P "Reader.nameOf" [recAtom (v 1)]
    let dn := pc P "Typing.atomName" [atom (v 1)]
    let nInv := (s.hyps P S T X₀).length
    let more := formsOk P S (v 3)
    let hyps := [Internal.instTerm [] [v 3] (passesφ P S T X₀ (formsOk P S))] ++
      s.hyps P S T X₀ ++
      [Term.eq (pc P "Typing.envNoms" [s.env]) (namesSnoc P (pc P "Typing.envNoms" [v 13]) dn),
        truth o (occInT P (memberAtomT P dn) s.fs), userNameT P nmR,
        Term.eq (get (pc P "Recognize.recognizer" [s.ms, m])) (defForm P (recAtom (v 1)) (v 0)),
        recDenT P S (s.rel P) s.tys s.names s.nums s.ms m (v 0)] ++ more
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (XA, csA, esA) := (at_ 0, at_ 1, at_ 3)
    let states (Γ : List Tree) : List Term :=
      (List.range (passesCtx T).length).map fun j ↦ at_ (4 + j) Γ
    let s₀A (Γ : List Tree) : Passes := passesAt (4 + (Γ.length - Γ₀.length)) (esA Γ)
    let s'A (Γ : List Tree) : Passes := { s₀A Γ with
      names := app (s₀A Γ).names (one (pc P "Reader.nameOf" [recAtom (csA Γ)]))
      terms := app (s₀A Γ).terms (one (get (pc P "Reader.resolve" [(s₀A Γ).tys, (s₀A Γ).names,
        pc P "Reader.expandNums" [(s₀A Γ).nums, XA Γ], nil]))) }
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hMore := 1 + nInv + 5
    let some d := (at' "the marker" <|
        applyThm K "markerReadAt"
          (fun Γ ↦ [XA Γ, csA Γ, at_ 2 Γ, nil, esA Γ] ++ states Γ ++ [at_ 13 Γ])
          ((List.range (nInv + 5)).map fun k ↦
            stage s!"blockEndAt: the hypothesis {k} at the marker" (hypOrK K (1 + k))) <|
        at' "the forms after" <| conjEs K (nInv + 1) fun inv Γ Φ ψ ↦
        dAllE L K.G K.E 0 ((s'A Γ).dv) (
          K.allEΓ (fun Γ ↦ (s'A Γ).env) <| K.allEΓ (fun Γ ↦ (s'A Γ).rej) <|
          K.allEΓ (fun Γ ↦ (s'A Γ).tys) <| K.allEΓ (fun Γ ↦ (s'A Γ).nums) <|
          K.allEΓ (fun Γ ↦ (s'A Γ).names) <| K.allEΓ (fun Γ ↦ (s'A Γ).terms) <|
          K.allEΓ (fun Γ ↦ (s'A Γ).ms) <| K.allEΓ (fun Γ ↦ (s'A Γ).fs) <|
          last fun iIH ↦ impEs L iIH
            ((List.range nInv).map (fun k ↦
                stage s!"blockEndAt: the hypothesis {k} after the block" <|
                  if k = 11 then unfoldBothK K (T.q + 6 + 2 * nFolds) (inv k)
                  else hypOrK K (inv k)) ++
              (List.range more.length).map fun k ↦
                stage "blockEndAt: the rest's kinds" (hypOrK K (hMore + k))) <|
          last fun iAfter ↦ dImpE L (inv nInv)
            (stage "blockEndAt: the conclusion after the block" (K.byHyp iAfter))
            (stage "blockEndAt: the conclusion" (last K.byHyp))) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "blockEndAt: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at the forms that remain after a datatype's block, at the block's marker: the
marker leaves states of which the hypotheses hold again, at which the hypothesis on the forms
after gives the conclusion. Where the program's forms do not refer to the datatype's
recognizer the states are as before ({name}`markerSkipped`); where they do, the marker's
datatype has an index among the markers' names ({name}`ctorsIndexed`), the recognizer the
writer gives is the definition of the recognizer's atom as the writer's abstraction, which
denotes a function deciding membership ({name}`recognizerAt`), and the reader has read it
({name}`blockEndAt`). In the context of the characters of the datatype's atom, the
constructors' entries, the forms that remain, the states and the recognizers' environment. -/
def blockEnd (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("blockEnd", fun ix E ↦ do
    let K : Kit := ⟨markerProg P, S, E, ix, ["eraseMarker", "recAtMarker"] ++ lookupEqNames⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"blockEnd @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "blockEnd: no partition" fun _ ↦ none
    let atom (cs : Term) : Term := nodeT (Term.pair (numeral 1) cs)
    let s : Passes := { passesAt 3 (v 2) with
      ws := some (consT treeTy (markerT (atom (v 0)) (v 1)) nil), recEnv := some (v 12) }
    let Γ₀ := [Ls, Ls, Ls] ++ passesCtx T ++ [T.envTy]
    let nmR := pc P "Reader.nameOf" [pc P "Datatype.memberName" [atom (v 0)]]
    let nInv := (s.hyps P S T X₀).length
    let more := formsOk P S (v 2)
    let hyps := [Internal.instTerm [] [v 2] (passesφ P S T X₀ (formsOk P S))] ++
      s.hyps P S T X₀ ++ blockFacts P s (v 12) (v 0) ++ [userNameT P nmR, digitsFixedT P] ++ more
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (csA, xsA, esA, fsA, msA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4)
    let (namesA, numsA, tysA) := (at_ 6, at_ 7, at_ 8)
    let states (Γ : List Tree) : List Term :=
      (List.range (passesCtx T).length).map fun j ↦ at_ (3 + j) Γ
    let dA (Γ : List Tree) : Term := atom (csA Γ)
    let mA (Γ : List Tree) : Term := markerT (dA Γ) (xsA Γ)
    let dnA (Γ : List Tree) : Term := pc P "Typing.atomName" [dA Γ]
    let sA (Γ : List Tree) : Passes := { passesAt (3 + (Γ.length - Γ₀.length)) (esA Γ) with
      ws := some (consT treeTy (mA Γ) nil), recEnv := some (at_ 12 Γ) }
    let s₀A (Γ : List Tree) : Passes := passesAt (3 + (Γ.length - Γ₀.length)) (esA Γ)
    let childT := (primT Kernel.Prim.child).getD Term.star
    -- the writer's abstraction, of the closure of the marker's datatype, its first child
    let XA (Γ : List Tree) : Term := recForm P (pc P "Recognize.closure" [msA Γ,
      apps childT [mA Γ, leafT (numeral 0)]]) (msA Γ)
    let recA (Γ : List Tree) : Term := pc P "Recognize.recognizer" [msA Γ, mA Γ]
    let referred (Γ : List Tree) : Term := occInT P (memberAtomT P (dnA Γ)) (fsA Γ)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    let inv₀ (k : ℕ) : ℕ := 1 + k
    let (hO, hNames, hKws, hMk, hStatic) := (inv₀ 2, inv₀ 8, inv₀ 9, inv₀ 22, inv₀ 23)
    let (hNoms, hUserR, hDigits, hMore) :=
      (1 + nInv, 1 + nInv + 3, 1 + nInv + 4, 1 + nInv + 5)
    -- a hypothesis that is the goal as written
    let same (i : ℕ) : Deducer := fun Γ Φ ψ ↦
      (Φ[i]?).bind fun h ↦ if h == ψ then dHyp Γ Φ ψ else none
    -- the writer's builders of the recognizer's tests kept folded
    let K₂ : Kit := { K with P := { K.P with folded := K.P.folded ++ ["Recognize.ctorTest",
      "Recognize.dataTest", "Recognize.markerOf", "Recognize.closure"] } }
    let skipped : Deducer := at' "not referred to" <|
      applyThm K "markerSkipped" (fun Γ ↦ [csA Γ, xsA Γ, nil, esA Γ] ++ states Γ ++ [at_ 12 Γ])
        ((List.range nInv).map (fun k ↦
            stage s!"blockEnd: the hypothesis {k} at the marker" (hypOr (inv₀ k))) ++
          [stage "blockEnd: the datatypes" (hypOr hNoms),
            stage "blockEnd: not referred to" (dImpI L (lastFalse K))]) <|
      conjEs K (nInv + 1) fun inv Γ Φ ψ ↦
      dAllE L K.G K.E 0 ((s₀A Γ).dv) (
        K.allEΓ (fun Γ ↦ (s₀A Γ).env) <| K.allEΓ (fun Γ ↦ (s₀A Γ).rej) <|
        K.allEΓ (fun Γ ↦ (s₀A Γ).tys) <| K.allEΓ (fun Γ ↦ (s₀A Γ).nums) <|
        K.allEΓ (fun Γ ↦ (s₀A Γ).names) <| K.allEΓ (fun Γ ↦ (s₀A Γ).terms) <|
        K.allEΓ (fun Γ ↦ (s₀A Γ).ms) <| K.allEΓ (fun Γ ↦ (s₀A Γ).fs) <|
        last fun iIH ↦ impEs L iIH
          ((List.range nInv).map (fun k ↦
              stage s!"blockEnd: the hypothesis {k} after the block" <|
                if k = 11 then unfoldBothK K (T.q + 6 + 2 * nFolds) (inv k)
                else hypOr (inv k)) ++
            (List.range more.length).map fun k ↦
              stage "blockEnd: the rest's kinds" (hypOr (hMore + k))) <|
        last fun iAfter ↦ dImpE L (inv nInv)
          (stage "blockEnd: the conclusion after the block" (K.byHyp iAfter))
          (stage "blockEnd: the conclusion" (last K.byHyp))) Γ Φ ψ
    let read : Deducer := at' "referred to" <|
      decideOpt K recA (at' "no recognizer" (K.hypFalse hO)) <|
      normHyps K [hMk] <| K.conjE <| last fun iMkRest ↦
      dImpE L (iMkRest - 1) (at' "a marker" (K.solve 3)) <| last fun iCtors ↦
      applyThm K "ctorsIndexed" (fun Γ ↦ [xsA Γ, dA Γ, msA Γ])
        [at' "the marker's constructors" (eqByHyp K iCtors)] <| last fun iIdx ↦
      applyThm K "recognizerAt" (fun Γ ↦ [mA Γ, msA Γ, tysA Γ, namesA Γ, numsA Γ,
          (sA Γ).rel P])
        [at' "a recognizer" (K.solve 3), hypOr hKws, hypOr hNames, hypOr hStatic,
          hypOr hDigits, at' "the datatype's index" (K.byHyp iIdx)] <|
      K.conjE <| fun Γ₃ Φ₃ ψ₃ ↦
      let (iDefEq, iEx) := (Φ₃.length - 2, Φ₃.length - 1)
      (applyThm K "blockEndAt" (fun Γ ↦ XA Γ :: (List.range 13).map fun j ↦ at_ j Γ)
        ((List.range (1 + nInv)).map (fun i ↦ at' s!"the hypothesis {i}" (same i)) ++
          [at' "the datatypes" (hypOr hNoms), at' "referred to" (K.solve 3),
            at' "the name's origin" (hypOr hUserR),
            at' "the definition" (dRwBy (evalRw K.G K.E [.hyp iDefEq] .full) K₂.byNorm),
            at' "the denotation" (same iEx)] ++
          (List.range more.length).map fun k ↦ at' "the rest's kinds" (same (hMore + k))) <|
        at' "the conclusion" dHyp) Γ₃ Φ₃ ψ₃
    let some d := decideIn K referred skipped read a.ctx a.hyps a.concl
      | dbgTrace "blockEnd: not proved" fun _ ↦ none
    pure (a, d))

/-- The definition the expansion's reading of a constructor writes, where the constructor has a
variable field: the definition of the constructor's atom as the body {name}`ctorVarDefT`, the
term of the constructors' soundness ({lit}`ctorVar`). The constructor's tests of a variable
field decided. In the context of the constructor's elements after its atom, the atom, its
position and the datatype's name. -/
def ctorDeclVar (P : Prog) (S : Defs) : Step :=
  ("ctorDeclVar", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [Ls, treeTy, treeTy, treeTy]
    let (rest, nm, j, d) := (v 0, v 1, v 2, v 3)
    let ltT ← primT Kernel.Prim.lt
    let subT ← primT Kernel.Prim.sub
    let c := nodeT (Term.pair (numeral 2) (consT treeTy nm rest))
    let nr := pc P "Datatype/Txs.length" [rest]
    let more := apps ltT [leafT (numeral 1), nr]
    let amp := pc P "Datatype.namedTx"
      [pc P "Datatype.nthTx" [rest, apps subT [nr, leafT (numeral 2)]], pc P "Datatype.kwAmp" []]
    let decl := pc P "Datatype.ctorDecl" [d, j, c]
    let a : Internal.Thm := ⟨0, Γ, [truth P.o (varFlagT P rest)],
      Term.eq (Term.snd (Term.snd decl))
        (defForm P nm (ctorVarDefT P (call D.children [] [d]) j rest))⟩
    let at_ (t : Term) (Γ' : List Tree) : Term := sh (Γ'.length - Γ.length) t
    let written := byNormTraced K "ctorDeclVar"
    let some d := decideIn K (at_ more) (K.hypFalse 0)
        (decideIn K (at_ amp) (K.hypFalse 0) written) a.ctx a.hyps a.concl
      | dbgTrace "ctorDeclVar: not proved" fun _ ↦ none
    pure (a, d))

/-- The entry a marker holds of a constructor with a variable field: its position, its field
types' representations, the test of a variable field, which holds, and the representation of
the variable field's type. Of the declarations, the position and the constructor's elements
after its atom. -/
def entryVarT (P : Prog) (dv j rest : Term) : Term :=
  node0 (consT treeTy j (consT treeTy (node0 (repsT P dv (varFieldsT P rest)))
    (consT treeTy (varFlagT P rest) (consT treeTy
      (pc P "Datatype.expandAliases" [dv, varTypeT P rest]) (nilT treeTy)))))

/-- The entries a marker holds of the declaration of a constructor with a variable field before
others: the constructor's entry ({name}`entryVarT`) before the others' entries. In the context
of the constructor's elements after its atom, the atom, its position, the datatype's name, the
declarations, the datatype's atom and the other declarations. -/
def ctorEntryVar (P : Prog) (S : Defs) : Step :=
  ("ctorEntryVar", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [Ls, treeTy, treeTy, treeTy, Ls, treeTy, Ls]
    let (rest, nm, j, d, dv, dA, ds) := (v 0, v 1, v 2, v 3, v 4, v 5, v 6)
    let ltT ← primT Kernel.Prim.lt
    let subT ← primT Kernel.Prim.sub
    let c := nodeT (Term.pair (numeral 2) (consT treeTy nm rest))
    let nr := pc P "Datatype/Txs.length" [rest]
    let more := apps ltT [leafT (numeral 1), nr]
    let amp := pc P "Datatype.namedTx"
      [pc P "Datatype.nthTx" [rest, apps subT [nr, leafT (numeral 2)]], pc P "Datatype.kwAmp" []]
    let decl := pc P "Datatype.ctorDecl" [d, j, c]
    let a : Internal.Thm := ⟨0, Γ, [truth P.o (varFlagT P rest)],
      Term.eq (entriesT P dv dA (consT treeTy (Term.fst (Term.snd decl)) ds))
        (consT treeTy (entryVarT P dv j rest) (entriesT P dv dA ds))⟩
    let at_ (t : Term) (Γ' : List Tree) : Term := sh (Γ'.length - Γ.length) t
    let written := byNormTraced K "ctorEntryVar"
    let some d := decideIn K (at_ more) (K.hypFalse 0)
        (decideIn K (at_ amp) (K.hypFalse 0) written) a.ctx a.hyps a.concl
      | dbgTrace "ctorEntryVar: not proved" fun _ ↦ none
    pure (a, d))

/-- The body of the definition of a constructor without a variable field, of the characters of
the datatype's atom, the constructor's position and its fields' types: the abstractions over
the fields' binders around the coercion to the datatype of the node of the position over the
fields' values. -/
def ctorDefT (P : Prog) (csd j fs : Term) : Term :=
  let nr := pc P "Datatype/Txs.length" [fs]
  let z := pc P "Datatype.sx2" [pc P "Datatype.aNil" [], pc P "Datatype.aT" []]
  nestT P (binderFold P nr fs) (ctorBody P csd j nr z fs)

/-- The soundness at the forms that remain within a datatype's block, a step at the definition
of a constructor, without a variable field or, where {lit}`var` holds, with one: given the
soundness at the forms after the definition, at all states of which the hypotheses and the
block's facts ({name}`blockFacts`, {name}`blockStatics`) hold, the hypotheses at states with
the definition pending give the conclusion. The definition is sound at the states
({name}`ctorSoundAt`, {name}`ctorSoundVarAt`): the aliases of the declarations before the
block are those of the declarations ({lit}`aliasSameBack`), the typing reads the datatype's
atom as the datatype ({name}`dataRead`), and the marker's constructors, those its datatype's
atom finds, have the constructor's entry after others and before others ({name}`anyAt`),
whose test is the walk's, the position's label its own ({lit}`eqSelfB`). The definition read
leaves states of which the hypotheses hold again ({name}`writtenInv`), as do the block's
facts, which read no definition. In the context of the constructor's elements after its atom,
the atom, the pending forms after, the forms that remain, the states, the recognizers'
environment,
the characters of the datatype's atom, the constructor's position, the declarations before
the block, the marker's entries, and those before and after the constructor's. -/
def blockCtor (P : Prog) (S : Defs) (T : Defs3) (var : Bool) : Step :=
  (if var then "blockCtorVar" else "blockCtor", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseDefForm", "recAtThree"] ++ lookupEqNames⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"blockCtor @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "blockCtor: no partition" fun _ ↦ none
    let atom (cs : Term) : Term := nodeT (Term.pair (numeral 1) cs)
    let named (cs : Term) (kw : String) : Term := pc P "Reader.named" [atom cs, pc P kw []]
    -- the definition's body and the marker's entry, of the characters, the position and the
    -- constructor's elements, and of the declarations before the block
    let bodyOf (csd j xs : Term) : Term :=
      if var then ctorVarDefT P csd j xs else ctorDefT P csd j xs
    let entryOf (dv j xs : Term) : Term := if var then entryVarT P dv j xs else entryT P dv j xs
    let s : Passes := { passesAt 4 (v 3) with
      ws := some (consT treeTy (defForm P (v 1) (bodyOf (v 14) (v 15) (v 0))) (v 2)),
      recEnv := some (v 13) }
    let Γ₀ := [Ls, treeTy, Ls, Ls] ++ passesCtx T ++ [T.envTy, Ls, treeTy, Ls, Ls, Ls, Ls]
    -- the soundness at the forms after, under the states' quantifiers
    let sR : Passes := { passesAt 0 (v 12) with ws := some (v 11), recEnv := some (v 22) }
    let after := (passesCtx T).foldl (fun b A ↦ Internal.Logic.all o A (Term.lam A b))
      ((sR.hyps P S T X₀ ++ blockFacts P sR (v 22) (v 23) ++
          blockStatics P sR (v 23) (v 25) (v 26)).foldr (Internal.Logic.imp o)
        (sR.concl P T X₀))
    let nInv := (s.hyps P S T X₀).length
    let hyps := [after] ++ s.hyps P S T X₀ ++ blockFacts P s (v 13) (v 14) ++
      [notTest o (named (v 14) "Reader.kwT"), notTest o (named (v 14) "Reader.kwUnit")] ++
      blockStatics P s (v 14) (v 16) (v 17) ++
      [Term.eq (v 17) (pc P "Prelude.append" [v 18,
          consT treeTy (entryOf (v 16) (v 15) (v 0)) (v 19)]),
        (if var then truth o (varFlagT P (v 0)) else notTest o (varFlagT P (v 0))),
        userNameT P (pc P "Reader.nameOf" [v 1]),
        digitsFixedT P]
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (fsA, nmA, wsA, esA) := (at_ 0, at_ 1, at_ 2, at_ 3)
    let (msA, termsA, namesA, numsA, tysA, EA, dvA) :=
      (at_ 5, at_ 6, at_ 7, at_ 8, at_ 9, at_ 11, at_ 12)
    let (ErA, csdA, jA, dv₀A, preA, postA) := (at_ 13, at_ 14, at_ 15, at_ 16, at_ 18, at_ 19)
    let XA (Γ : List Tree) : Term := bodyOf (csdA Γ) (jA Γ) (fsA Γ)
    let states (Γ : List Tree) : List Term :=
      (List.range (passesCtx T).length).map fun k ↦ at_ (4 + k) Γ
    let sA (Γ : List Tree) : Passes := { passesAt (4 + (Γ.length - Γ₀.length)) (esA Γ) with
      ws := some (consT treeTy (defForm P (nmA Γ) (XA Γ)) (wsA Γ)), recEnv := some (ErA Γ) }
    let s'A (Γ : List Tree) : Passes := (sA Γ).written P (nmA Γ) (XA Γ) (wsA Γ)
    let RA (Γ : List Tree) : Term := (sA Γ).rel P
    let entryA (Γ : List Tree) : Term := entryOf (dv₀A Γ) (jA Γ) (fsA Γ)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    let inv₀ (k : ℕ) : ℕ := 1 + k
    let (hNoms, hNoAbbr, hHas) := (1 + nInv, 2 + nInv, 3 + nInv)
    let (hKwT, hKwU, hSame, hCtors, _, hPlain, hUser, hDigits) :=
      (4 + nInv, 5 + nInv, 6 + nInv, 7 + nInv, 8 + nInv, 9 + nInv, 10 + nInv, 11 + nInv)
    -- the marker's constructors have the constructor's: its entry's test is the walk's
    let listed : Deducer := dAllI L <| dImpI L <| fun Γ₅ Φ₅ ψ₅ ↦
      let (hWalk, n₅) := (Φ₅.length - 1, Γ₅.length)
      let test (Γ : List Tree) : Term := Term.lam treeTy (pc P "Typing.ctorOk"
        [Term.snd (sh 1 (RA Γ)), v 0, leafT (call D.lab [] [sh 1 (jA Γ)]),
          sh 1 (v (Γ.length - n₅))])
      (K.cutThm "anyAt" (fun Γ ↦ [preA Γ]) <| K.allEΓ postA <| K.allEΓ entryA <|
        K.allEΓ test <|
        K.impE (at' "the constructor's entry" <|
          K.cutThm "eqSelfB" (fun Γ ↦ [call D.lab [] [jA Γ]]) <| normLastK K <|
          K.byHyp hWalk) <|
        at' "the marker's constructors" (last K.byHyp)) Γ₅ Φ₅ ψ₅
    let some d := (at' "the aliases before the block" <|
        applyThm K "aliasSameBack" (fun Γ ↦ [dv₀A Γ, dvA Γ, EA Γ, msA Γ, tysA Γ])
          [hypOr hSame, hypOr (inv₀ 18), hypOr (inv₀ 19), hypOr (inv₀ 20)] <|
        K.conjE <| K.conjE <| fun Γ₁ Φ₁ ψ₁ ↦
        let (iAl, iAlKw) := (Φ₁.length - 4, Φ₁.length - 2)
        (at' "the datatype read" <|
          applyThm K "dataRead" (fun Γ ↦ [csdA Γ, EA Γ])
            [hypOr hKwT, hypOr hKwU, hypOr hNoAbbr, hypOr hHas] <| last fun iRead ↦
          let step : Deducer := (normHyps K [hCtors] <| at' "the definition sound" <|
              applyThm K (if var then "ctorSoundVarAt" else "ctorSoundAt")
                (fun Γ ↦ [fsA Γ, csdA Γ, jA Γ] ++ (if var then [] else [noRestT P (dv₀A Γ)]) ++
                  [dv₀A Γ, Term.snd (kcRun P (termsA Γ) kcInit), numsA Γ, namesA Γ, tysA Γ,
                  EA Γ, RA Γ])
                [at' "the numerals" (hypOr (inv₀ 7)), at' "the keywords" (hypOr (inv₀ 9)),
                  at' "related" (hypOr (inv₀ 6)), at' "the names" (hypOr (inv₀ 8)),
                  at' "the names' origin" (hypOr (inv₀ 16)), at' "no sort" (hypOr (inv₀ 17)),
                  at' "the aliases" (K.byHyp iAl), at' "the aliases of types read first"
                    (hypOr iAlKw),
                  at' "the markers and the numerals" (K.byHyp (inv₀ 23)),
                  at' "the digits" (hypOr hDigits),
                  at' "the datatype's reading" (fun Γ Φ ψ ↦
                    (dHyp Γ Φ ψ).orElse fun _ ↦ eqByHyp K iRead Γ Φ ψ),
                  at' "the constructor listed" listed] <| last fun iSound ↦
              at' "the definition read" <|
              applyThm K "writtenInv"
                (fun Γ ↦ [XA Γ, nmA Γ, wsA Γ, esA Γ] ++ states Γ ++ [ErA Γ])
                ((List.range nInv).map (fun k ↦
                    stage s!"blockCtor: the hypothesis {k} at the states" (hypOr (inv₀ k))) ++
                  [stage "blockCtor: the body sound" (K.byHyp iSound),
                    stage "blockCtor: the name's origin" (hypOr hUser)]) <|
              at' "the forms after" <| conjEs K (nInv + 1) fun inv Γ Φ ψ ↦
              dAllE L K.G K.E 0 ((s'A Γ).dv) (
                K.allEΓ (fun Γ ↦ (s'A Γ).env) <| K.allEΓ (fun Γ ↦ (s'A Γ).rej) <|
                K.allEΓ (fun Γ ↦ (s'A Γ).tys) <| K.allEΓ (fun Γ ↦ (s'A Γ).nums) <|
                K.allEΓ (fun Γ ↦ (s'A Γ).names) <| K.allEΓ (fun Γ ↦ (s'A Γ).terms) <|
                K.allEΓ (fun Γ ↦ (s'A Γ).ms) <| K.allEΓ (fun Γ ↦ (s'A Γ).fs) <|
                last fun iH ↦ impEs L iH
                  ((List.range nInv).map (fun k ↦
                      stage s!"blockCtor: the hypothesis {k} after the definition"
                        (hypOr (inv k))) ++
                    [stage "blockCtor: the datatypes after" (eqByHyp K hNoms),
                      stage "blockCtor: no abbreviation after" (K.byHyp hNoAbbr),
                      stage "blockCtor: a datatype after" (K.byHyp hHas),
                      stage "blockCtor: the aliases after" (hypOr hSame),
                      stage "blockCtor: the marker's constructors after" (hypOr hCtors)]) <|
                last fun iAfter ↦ dImpE L (inv nInv)
                  (stage "blockCtor: the conclusion after the definition" (K.byHyp iAfter))
                  (stage "blockCtor: the conclusion" (last K.byHyp))) Γ Φ ψ)
          if var then
            decideIn K (fun Γ ↦ varFlagT P (fsA Γ)) (at' "no variable field" (K.hypFalse hPlain))
              step
          else
            decideIn K (fun Γ ↦ varFlagT P (fsA Γ)) step
              (at' "a variable field" (refuteNot K hPlain))) Γ₁ Φ₁ ψ₁) a.ctx a.hyps a.concl
      | dbgTrace s!"blockCtor {var}: not proved" fun _ ↦ none
    pure (a, d))

/-- The program of the steps within a datatype's block: the passes' steps kept folded
({name}`passProg`), and a constructor's reading, whose parts at a constructor are equations
({lit}`ctorFlag`, {name}`ctorDeclPlain`, {name}`ctorEntry`). -/
def blockProg (P : Prog) : Prog :=
  { passProg P with folded := (passProg P).folded ++ ["Datatype.ctorDecl"] }

/-- Whether a constructor's reading finds it well formed: a list whose first element is an
atom. The sides in the normal forms of the rules within a block ({name}`blockProg`), the
reading unfolded in the proof. In the context of the constructor, its position and the
datatype's name. -/
def ctorFlag (P : Prog) (S : Defs) : Step :=
  ("ctorFlag", fun ix E ↦ do
    let K : Kit := ⟨blockProg P, S, E, ix, []⟩
    let Γ := [treeTy, treeTy, treeTy]
    let lhs := Term.fst (pc P "Datatype.ctorDecl" [v 2, v 1, v 0])
    let rhs := pc P "Prelude.and" [pc P "Datatype.isListTx" [v 0], pc P "Datatype.isAtomTx"
      [pc P "Datatype.nthTx" [pc P "Datatype.elems" [v 0], leafT bnilT]]]
    let some l := nfE K.G K.E (K.rules []) Γ lhs | dbgTrace "ctorFlag: left" fun _ ↦ none
    let some r := nfE K.G K.E (K.rules []) Γ rhs | dbgTrace "ctorFlag: right" fun _ ↦ none
    let some d := byMode .full K.G K.E 0
        (K.rules [] ++ [.delta (P.idx "Datatype.ctorDecl")]) Γ [] l r
      | dbgTrace "ctorFlag: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- A goal that is a hypothesis as written, or the hypothesis rewritten by one equation, a
hypothesis, alone; else by normalization, which is traced. -/
def rawHypK (K : Kit) (iEq h : ℕ) : Deducer := fun Γ Φ ψ ↦
  (dHyp Γ Φ ψ).orElse fun _ ↦
    (dRwHyp (evalRw K.G K.E [.hyp iEq] .full) h dHyp Γ Φ ψ).orElse fun _ ↦
      dbgTrace s!"rawHypK: the hypothesis {h} by normalization" fun _ ↦ K.byHyp h Γ Φ ψ

/-- The pending forms of a datatype's block at a list of its constructors: the constructors'
definitions ({name}`ctorDefsT`) before the marker of the datatype's atom and the marker's
entries. Of the characters of the datatype's atom and the number of all its constructors. -/
def blockPendingT (P : Prog) (csd nc xs cs : Term) : Term :=
  let Da := nodeT (Term.pair (numeral 1) csd)
  pc P "Datatype/Txs.append" [ctorDefsT P (pc P "Datatype.atomName" [Da]) nc cs,
    pc P "Datatype/Txs.single" [markerT Da xs]]

/-- The hypotheses of the soundness at the forms that remain within a datatype's block, at a
list of its constructors: the hypothesis on the forms after the block, the hypotheses at states
with the constructors' definitions and the marker pending ({name}`blockPendingT`), the block's
facts ({name}`blockFacts`, {name}`blockStatics`), that the datatype's atom is named as neither
type the typing reads first, that the marker's entries are those of the constructors after
others, that the constructors are well formed and named by none of the implementation's
names, as the recognizer is, that the digits are fixed, and the kinds of
the forms after. With the states at the constructors. -/
def blockHyps (P : Prog) (S : Defs) (T : Defs3) (X₀ es Er csd nc dv₀ xs pre cs : Term)
    (st : Passes) : Passes × List Term :=
  let o := P.o
  let Da := nodeT (Term.pair (numeral 1) csd)
  let d := pc P "Datatype.atomName" [Da]
  let s : Passes := { st with ws := some (blockPendingT P csd nc xs cs), recEnv := some Er }
  let named (kw : String) : Term := pc P "Reader.named" [Da, pc P kw []]
  let elems := pc P "Datatype.elems" [v 0]
  (s, [Internal.instTerm [] [es] (passesφ P S T X₀ (formsOk P S))] ++ s.hyps P S T X₀ ++
    blockFacts P s Er csd ++
    [notTest o (named "Reader.kwT"), notTest o (named "Reader.kwUnit")] ++
    blockStatics P s csd dv₀ xs ++
    [Term.eq xs (pc P "Prelude.append" [pre, entriesT P dv₀ Da (ctorDeclsT P d nc cs)]),
      truth o (Term.fst (Term.snd (ctorsFold P d nc cs))),
      S.allL (Term.lam treeTy (userNameT P (pc P "Reader.nameOf"
        [pc P "Datatype.nthTx" [elems, leafT bnilT]]))) cs,
      userNameT P (pc P "Reader.nameOf" [pc P "Datatype.memberName" [Da]]),
      digitsFixedT P] ++ formsOk P S es)

/-- The soundness at the forms that remain within a datatype's block, at the definitions of a
list of its constructors and the marker after them, at all states and block's parts
({name}`blockHyps`): by induction on the constructors. At none the marker is pending
({name}`blockEnd`). At a constructor before others, the constructor, well formed, is a list of
an atom before its fields' types, with a variable field or without; its definition is pending
before
the others' and the marker, its entry is before the others' among the marker's entries, after
those before with it ({lit}`appendSnoc`), and the step at its definition
({name}`blockCtor`) gives the conclusion from the induction hypothesis at the states its
reading leaves. In the context of the constructors, under the forms that remain, the
recognizers' environment, the characters of the datatype's atom, the number of all its
constructors, the declarations before the block, the marker's entries, those before the
constructors', and the states. -/
def ctorsInv (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("ctorsInv", fun ix E ↦ do
    let K : Kit := ⟨blockProg P, S, E, ix, ["eraseDefForm", "recAtThree"] ++ lookupEqNames⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"ctorsInv @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "ctorsInv: no partition" fun _ ↦ none
    let subT ← primT Kernel.Prim.sub
    let atom (cs : Term) : Term := nodeT (Term.pair (numeral 1) cs)
    -- under the quantifiers: the states v0 to v8, those before v9, the entries v10, the
    -- declarations before v11, the number v12, the characters v13, the recognizers'
    -- environment v14, the forms that remain v15, the constructors v16
    let (s, ants) := blockHyps P S T X₀ (v 15) (v 14) (v 13) (v 12) (v 11) (v 10) (v 9) (v 16)
      (passesAt 0 (v 15))
    let nAnts := ants.length
    let nStates := (passesCtx T).length
    let φ := ([Ls, T.envTy, Ls, treeTy, Ls, Ls, Ls] ++ (passesCtx T).reverse).foldr
      (fun A b ↦ Internal.Logic.all o A (Term.lam A b))
      (ants.foldr (Internal.Logic.imp o) (s.concl P T X₀))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    let intro (k : Deducer) : Deducer :=
      repeatK (7 + nStates) (dAllI L) (repeatK nAnts (dImpI L) k)
    -- the variables by their positions from the outermost
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    -- no constructors: the marker is pending
    let base : Deducer := intro fun Γ₁ Φ₁ ψ₁ ↦
      let h (i : ℕ) : ℕ := Φ₁.length - nAnts + i
      (cutBy (fun Γ ↦ Term.eq (blockPendingT P (at_ 2 Γ) (at_ 3 Γ) (at_ 5 Γ) (nilT treeTy))
          (consT treeTy (markerT (atom (at_ 2 Γ)) (at_ 5 Γ)) (nilT treeTy)))
        (at' "the marker pending" (byNormTraced K "ctorsInv: the marker pending")) <|
        last fun iWs ↦
        applyThm K "blockEnd" (fun Γ ↦ [at_ 2 Γ, at_ 5 Γ, at_ 0 Γ] ++
          ((List.range nStates).map fun k ↦ at_ (15 - k) Γ) ++ [at_ 1 Γ])
        ((List.range 28).map (fun i ↦
            stage s!"ctorsInv: the hypothesis {i} at the marker" (rawHypK K iWs (h i))) ++
          [hypOr (h 35), hypOr (h 36), hypOr (h 37)]) <|
        at' "the conclusion at the marker" <|
        dRwBy (evalRw K.G K.E [.hyp iWs] .full) (last hypOr)) Γ₁ Φ₁ ψ₁
    -- a constructor before others: the head 0, the others 1, then as above from 2
    let step : Deducer := intro fun Γ₁ Φ₁ ψ₁ ↦
      let h (i : ℕ) : ℕ := Φ₁.length - nAnts + i
      let (cA, tlA, esA, ErA, csdA, ncA, dv₀A, xsA, preA) :=
        (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5, at_ 6, at_ 7, at_ 8)
      let states (Γ : List Tree) : List Term := (List.range nStates).map fun k ↦ at_ (17 - k) Γ
      let DaA (Γ : List Tree) : Term := atom (csdA Γ)
      let dA (Γ : List Tree) : Term := pc P "Datatype.atomName" [DaA Γ]
      let foldA (Γ : List Tree) : Term := ctorsFold P (dA Γ) (ncA Γ) (tlA Γ)
      let jA (Γ : List Tree) : Term :=
        apps subT [apps subT [ncA Γ, leafT (numeral 1)], Term.fst (foldA Γ)]
      let wsA (Γ : List Tree) : Term := blockPendingT P (csdA Γ) (ncA Γ) (xsA Γ) (tlA Γ)
      let postA (Γ : List Tree) : Term :=
        entriesT P (dv₀A Γ) (DaA Γ) (ctorDeclsT P (dA Γ) (ncA Γ) (tlA Γ))
      -- the constructor a list of an atom before the fields' types
      let onList (n₂ iFlag : ℕ) : Deducer := fun Γ Φ ψ ↦
        K.listCase treeTy (v (Γ.length - n₂)) (at' "no atom" (K.hypFalse iFlag))
          (fun Γ₃ Φ₃ ψ₃ ↦
          let n₃ := Γ₃.length
          let nmA (Γ : List Tree) : Term := v (1 + (Γ.length - n₃))
          let fsA (Γ : List Tree) : Term := v (Γ.length - n₃)
          let ctor (var : Bool) (flag : Deducer) (iUserC iUserRest iWs : ℕ) : Deducer :=
            let entryA (Γ : List Tree) : Term :=
              if var then entryVarT P (dv₀A Γ) (jA Γ) (fsA Γ)
              else entryT P (dv₀A Γ) (jA Γ) (fsA Γ)
            let pre' (Γ : List Tree) : Term :=
              pc P "Prelude.append" [preA Γ, pc P "Prelude.single" [entryA Γ]]
            -- the soundness at the forms after the definition, by the induction hypothesis
            let after : Deducer := repeatK nStates (dAllI L) <| repeatK 29 (dImpI L) <|
              fun Γ₄ Φ₄ ψ₄ ↦
              let g (i : ℕ) : ℕ := Φ₄.length - 29 + i
              let st' (k : ℕ) (Γ : List Tree) : Term := v (k + (Γ.length - Γ₄.length))
              (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (esA Γ) (
                K.allEΓ ErA <| K.allEΓ csdA <| K.allEΓ ncA <| K.allEΓ dv₀A <| K.allEΓ xsA <|
                K.allEΓ pre' <|
                (List.range nStates).foldr (fun k d ↦ K.allEΓ (st' (nStates - 1 - k)) d) <|
                last fun iIH ↦ impEs L iIH
                  ([stage "ctorsInv: the forms after the block" (hypOr (h 0))] ++
                    (List.range 27).map (fun k ↦
                      stage s!"ctorsInv: the hypothesis {k} after the definition"
                        (hypOr (g k))) ++
                    [hypOr (h 28), hypOr (h 29), hypOr (g 27), hypOr (g 28),
                      stage "ctorsInv: the entries after" (
                        K.cutThm "appendSnoc" (fun Γ ↦ [preA Γ, entryA Γ, postA Γ]) <|
                        normLastK K <| eqByHyp K (h 32)),
                      stage "ctorsInv: the others well formed" (K.solve 3),
                      stage "ctorsInv: the others' names" (hypOr iUserRest),
                      hypOr (h 35), hypOr (h 36), hypOr (h 37)]) <|
                at' "the conclusion after the definition" (last hypOr)) Γ Φ ψ) Γ₄ Φ₄ ψ₄
            at' "the constructor's definition" <|
            applyThm K (if var then "blockCtorVar" else "blockCtor")
              (fun Γ ↦ [fsA Γ, nmA Γ, wsA Γ, esA Γ] ++ states Γ ++
                [ErA Γ, csdA Γ, jA Γ, dv₀A Γ, xsA Γ, preA Γ, postA Γ])
              ([at' "the forms after" after] ++
                (List.range 31).map (fun i ↦
                  stage s!"ctorsInv: the hypothesis {i} at the definition"
                    (rawHypK K iWs (h (1 + i)))) ++
                [stage "ctorsInv: the constructor's entry" (eqByHyp K (h 32)),
                  stage "ctorsInv: the variable field's test" flag,
                  stage "ctorsInv: the constructor's name" (K.byHyp iUserC),
                  hypOr (h 36)]) <|
            at' "the conclusion" (dRwBy (evalRw K.G K.E [.hyp iWs] .full) (last hypOr))
          (decideIn K (fun Γ ↦ pc P "Datatype.isAtomTx" [nmA Γ])
            (at' "the head no atom" (K.hypFalse iFlag)) <|
            decideIn K (fun Γ ↦ Term.fst (Term.snd (foldA Γ)))
              (at' "the others ill formed" (K.hypFalse iFlag)) <|
            normHyps K [h 34] <| K.conjE <| last fun iUserRest ↦
            -- the constructor's definition and its entry, equations, and the pending forms:
            -- the definition before the others' and the marker
            let path (var : Bool) : Deducer :=
              let flag : Deducer := if var then K.solve 3 else dImpI L (lastFalse K)
              let body (Γ : List Tree) : Term :=
                if var then ctorVarDefT P (csdA Γ) (jA Γ) (fsA Γ)
                else ctorDefT P (csdA Γ) (jA Γ) (fsA Γ)
              applyThm K (if var then "ctorDeclVar" else "ctorDeclPlain")
                (fun Γ ↦ [fsA Γ, nmA Γ, jA Γ, dA Γ])
                [at' "the variable field's test" flag] <| normLastK K <|
              applyThm K (if var then "ctorEntryVar" else "ctorEntry")
                (fun Γ ↦ [fsA Γ, nmA Γ, jA Γ, dA Γ, dv₀A Γ, DaA Γ,
                  ctorDeclsT P (dA Γ) (ncA Γ) (tlA Γ)])
                [at' "the variable field's test" flag] <| normLastK K <|
              cutBy (fun Γ ↦ Term.eq
                  (blockPendingT P (csdA Γ) (ncA Γ) (xsA Γ) (consT treeTy (cA Γ) (tlA Γ)))
                  (consT treeTy (defForm P (nmA Γ) (body Γ)) (wsA Γ)))
                (at' "the pending forms" (byNormTraced K "ctorsInv: the pending forms")) <|
              last fun iWs ↦ ctor var flag (iUserRest - 1) iUserRest iWs
            decideIn K (fun Γ ↦ varFlagT P (fsA Γ)) (path false) (path true)) Γ₃ Φ₃ ψ₃)
          Γ Φ ψ
      -- the constructor's flag, an equation, then the hypothesis that the constructors are
      -- well formed at it
      (K.cutThm "ctorFlag" (fun Γ ↦ [cA Γ, jA Γ, dA Γ]) <| normLastK K <|
        normHyps K [h 33] <| last fun iFlag ↦ K.treeNode (cA Γ₁) fun Γ₂ Φ₂ ψ₂ ↦
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          if bs.map Oitavem.rank == some 2 then onList Γ₂.length iFlag
          else at' "no list" (K.hypFalse iFlag)) 3 [] (v 1) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    listInduction "ctorsInv" φ base step)

/-- The soundness at the forms that remain after a datatype's declaration, a step of the
soundness at all states ({name}`passesφ`): the expansion's step ({lit}`xpDataDecl`) declares
the datatype and its constructors and writes the datatype's node, the constructors'
definitions and the marker, pending before the forms of the rest ({lit}`typedFormsApp`); the
declarations hold no alias ({name}`declsNoAlias`, {name}`findAliasAppend`), so that the aliases
are coherent as before ({lit}`aliasSame`). The datatype's node read leaves states of which the
hypotheses hold again ({name}`dataInv`), its atom's name fresh; the constructors' definitions
and the marker give the conclusion ({name}`ctorsInv`) at the block's facts: the typing
environment has the datatype after those before, its name without an abbreviation, the atom
named as neither type the typing reads first ({lit}`kwReserved`), and the marker, past the
definitions ({name}`kernelAfter`), is the one its datatype's atom finds. In the context of the
constructors, the datatype's atom, the head, the forms after and the states. -/
def stepData (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepData", fun ix E ↦ do
    let K : Kit := ⟨blockProg P, S, E, ix,
      ["eraseDefForm", "recAtThree", "appendNil", "eraseMarker"] ++ lookupEqNames⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let nil := nilT treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"stepData @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "stepData: no partition" fun _ ↦ none
    let equalT ← primT Kernel.Prim.equal
    let atom (cs : Term) : Term := nodeT (Term.pair (numeral 1) cs)
    let fa (n dv : Term) : Term := pc P "Datatype.findAlias" [n, dv]
    let e := nodeT (Term.pair (numeral 2) (consT treeTy (v 2) (consT treeTy (v 1) (v 0))))
    let s := passesAt 4 (consT treeTy e (v 3))
    let head := dataHead P S (v 2) (v 1) (v 0)
    let nInv := (s.hyps P S T X₀).length
    let hyps := [Internal.instTerm [] [v 3] (passesφ P S T X₀ (formsOk P S))] ++ head ++
      s.hyps P S T X₀ ++ formsOk P S (v 3)
    let Γ₀ := [Ls, treeTy, treeTy, Ls] ++ passesCtx T
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (csA, dAA, hA, esA) := (at_ 0, at_ 1, at_ 2, at_ 3)
    let (fsA, msA, termsA, namesA, numsA, tysA, rA, EA, dvA) :=
      (at_ 4, at_ 5, at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11, at_ 12)
    let (hGen, hData, hUsers, hUserR) := (1, 2, 3, 4)
    let inv₀ (k : ℕ) : ℕ := 1 + head.length + k
    let hMore := 1 + head.length + nInv
    let xsA (Γ : List Tree) : Term := consT treeTy (hA Γ) (consT treeTy (dAA Γ) (csA Γ))
    let eA (Γ : List Tree) : Term := nodeT (Term.pair (numeral 2) (xsA Γ))
    let xpA (Γ : List Tree) : Term := pc P "Datatype.xpStep" [xpState (dvA Γ) nil, eA Γ]
    let dTxA (Γ : List Tree) : Term := pc P "Datatype.atomName" [dAA Γ]
    let ncA (Γ : List Tree) : Term := pc P "Datatype/Txs.length" [csA Γ]
    let declsA (Γ : List Tree) : Term := ctorDeclsT P (dTxA Γ) (ncA Γ) (csA Γ)
    let defsA (Γ : List Tree) : Term := ctorDefsT P (dTxA Γ) (ncA Γ) (csA Γ)
    let dsA (Γ : List Tree) : Term := consT treeTy (pc P "Datatype.dataD" [dTxA Γ]) (declsA Γ)
    let dv'A (Γ : List Tree) : Term := pc P "Datatype/Decls.append" [dvA Γ, dsA Γ]
    let m₀A (Γ : List Tree) : Term := pc P "Datatype.marker" [dvA Γ, dAA Γ, dsA Γ]
    -- the forms pending after the datatype's node, and with it
    let restA (Γ : List Tree) : Term :=
      pc P "Datatype/Txs.append" [defsA Γ, pc P "Datatype/Txs.single" [m₀A Γ]]
    let writtenA (Γ : List Tree) : Term := consT treeTy (pc P "Typing.tData" [dAA Γ]) (restA Γ)
    let afterA (Γ : List Tree) : Term := typedForms P (esA Γ) (dv'A Γ)
    -- the states after the datatype's node
    let s₂A (Γ : List Tree) : Passes :=
      ({ passesAt (4 + (Γ.length - Γ₀.length)) (esA Γ) with dv := dv'A Γ }).declared P (dAA Γ)
        (restA Γ)
    let nmA (Γ : List Tree) : Term := pc P "Reader.nameOf" [dAA Γ]
    let csdA (Γ : List Tree) : Term := call D.children [] [dAA Γ]
    let DaA (Γ : List Tree) : Term := atom (csdA Γ)
    let dnA (Γ : List Tree) : Term := atomNameT (DaA Γ)
    let xsAllA (Γ : List Tree) : Term := entriesT P (dvA Γ) (DaA Γ)
      (ctorDeclsT P (pc P "Datatype.atomName" [DaA Γ]) (ncA Γ) (csA Γ))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    let eqOr (h : ℕ) : Deducer := fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦ eqByHyp K h Γ Φ ψ
    let same (dvX dvY : List Tree → Term) (Γ : List Tree) : Term :=
      Internal.Logic.all o treeTy (Term.lam treeTy
        (Term.eq (fa (v 0) (sh 1 (dvX Γ))) (fa (v 0) (sh 1 (dvY Γ)))))
    -- the constructors' definitions and the marker, at the states after the datatype's node
    let inner (inv : ℕ → ℕ) (iWf iSame : ℕ) : Deducer := at' "the constructors" <|
      applyThm K "atomNode" (fun Γ ↦ [dAA Γ]) [hypOr (inv (nInv + 1))] <|
      decideIn K (fun Γ ↦ pc P "Reader.isAtom" [dAA Γ]) (K.hypFalse (inv (nInv + 1))) <|
      decideIn K (fun Γ ↦ Term.fst (Term.snd (ctorsFold P (dTxA Γ) (ncA Γ) (csA Γ))))
        (at' "ill formed" (K.hypFalse iWf)) <|
      -- the datatype's atom is named as neither type the typing reads first: not reserved
      let kwNot (kw reserved : String) : Deducer :=
        let kwA : Term := pc P kw []
        decideIn K (fun Γ ↦ apps equalT [nmA Γ, kwA]) (dImpI L (lastFalse K))
          (K.cutThm "equalSound" (fun Γ ↦ [nmA Γ]) <| K.allEΓ (fun _ ↦ kwA) <|
            K.impE (K.solve 3) <| last fun iEq ↦ dImpE L (inv (nInv + 2))
              (dRwBy (evalRw K.G K.E [.hyp iEq] .full) (K.cutThm reserved (fun _ ↦ []) dHyp))
              (dFalse L dHyp))
      -- the datatype's name has no abbreviation: an alias would be abbreviated
      let noAbbr : Deducer := dImpI L <| last fun iAb ↦ fun Γ Φ ψ ↦
        dAllE L K.G K.E (inv₀ 18) (dnA Γ) (K.conjE <| fun Γ₁ Φ₁ ψ₁ ↦
          let iA := Φ₁.length - 2
          dImpE L iA (dImpI L <| last fun iAl ↦ fun Γ Φ ψ ↦
              dAllE L K.G K.E (inv₀ 20) (dnA Γ) (K.impE (K.byHyp iAl) <| last fun iTy ↦
                dImpE L (inv (nInv + 3)) (K.byHyp iTy) (dFalse L dHyp)) Γ Φ ψ)
            (last fun iNo ↦ dImpE L iNo (K.byHyp iAb) (dFalse L dHyp)) Γ₁ Φ₁ ψ₁) Γ Φ ψ
      -- the marker, past the definitions, is the one the datatype's atom finds
      let found : Deducer :=
        K.cutThm "appendSnoc" (fun Γ ↦ [defsA Γ, m₀A Γ, afterA Γ]) <| normLastK K <|
        K.cutThm "kernelAfter" (fun Γ ↦ [defsA Γ]) <|
        K.allEΓ (fun Γ ↦ consT treeTy (m₀A Γ) (afterA Γ)) <|
        K.allEΓ (fun Γ ↦ markerPred P (msA Γ)) <|
        K.impE (at' "the markers that remain" (K.byHyp (inv 22))) <| normLastK K <|
        K.conjE <| fun Γ Φ ψ ↦
        dImpE L (Φ.length - 2) (at' "a marker" (K.solve 3))
          (last fun iCtors ↦ at' "the marker's constructors" (eqByHyp K iCtors)) Γ Φ ψ
      -- the forms pending after the datatype's node: the constructors' definitions and the
      -- marker of the datatype's atom and the declarations' entries
      cutBy (fun Γ ↦ Term.eq (restA Γ) (blockPendingT P (csdA Γ) (ncA Γ) (xsAllA Γ) (csA Γ)))
        (at' "the pending forms" (byNormTraced K "stepData: the pending forms")) <|
      last fun iWs ↦
      K.cutThm "ctorsInv" (fun Γ ↦ [csA Γ]) <|
      K.allEΓ esA <| K.allEΓ EA <| K.allEΓ csdA <| K.allEΓ ncA <| K.allEΓ dvA <|
      K.allEΓ xsAllA <| K.allEΓ (fun _ ↦ nil) <|
      K.allEΓ (fun Γ ↦ (s₂A Γ).dv) <| K.allEΓ (fun Γ ↦ (s₂A Γ).env) <|
      K.allEΓ (fun Γ ↦ (s₂A Γ).rej) <| K.allEΓ (fun Γ ↦ (s₂A Γ).tys) <| K.allEΓ numsA <|
      K.allEΓ namesA <| K.allEΓ termsA <| K.allEΓ msA <| K.allEΓ fsA <|
      last fun iC ↦ impEs L iC
        ([stage "stepData: the forms after the block" (hypOr 0)] ++
          (List.range nInv).map (fun k ↦
            stage s!"stepData: the hypothesis {k} after the datatype's node"
              (rawHypK K iWs (inv k))) ++
          [stage "stepData: the datatypes" (byNormTraced K "stepData: the datatypes"),
            stage "stepData: no abbreviation" noAbbr,
            stage "stepData: a datatype" (K.cutThm "hasSnocNew"
              (fun Γ ↦ [pc P "Typing.envNoms" [EA Γ]]) <| K.allEΓ dnA <| last K.byHyp),
            stage "stepData: not the trees' type" (kwNot "Reader.kwT" "kwTReserved"),
            stage "stepData: not the unit type" (kwNot "Reader.kwUnit" "kwUnitReserved"),
            stage "stepData: the aliases" (hypOr iSame),
            stage "stepData: the marker found" found,
            stage "stepData: the entries" (byNormTraced K "stepData: the entries"),
            stage "stepData: well formed" (K.solve 3),
            stage "stepData: the constructors' names" (hypOr hUsers),
            stage "stepData: the recognizer's name" (K.byHyp hUserR),
            stage "stepData: the digits" (fun Γ Φ ψ ↦
              dConjE L (inv₀ 23) (K.conjE (K.conjE (last hypOr))) Γ Φ ψ),
            stage "stepData: the rest's kinds" (hypOr hMore)]) <|
      at' "the conclusion after the datatype's node" <|
        dRwBy (evalRw K.G K.E [.hyp iWs] .full) (last hypOr)
    -- the datatype's node
    let block (iWf : ℕ) : Deducer := at' "the declarations" <|
      cutBy (same dv'A dvA) (dAllI L fun Γ₁ Φ₁ ψ₁ ↦
        let n := Γ₁.length
        let x (Γ : List Tree) : Term := v (Γ.length - n)
        (K.cutThm "declsNoAlias" (fun Γ ↦ [csA Γ]) <| K.allEΓ dTxA <| K.allEΓ ncA <|
          K.allEΓ x <| normLastK K <|
          K.cutThm "findAliasAppend" (fun Γ ↦ [dvA Γ]) <| K.allEΓ dsA <| K.allEΓ x <|
          K.impE (byNormTraced K "stepData: no alias") <| last eqOr) Γ₁ Φ₁ ψ₁) <|
      last fun iSame ↦
      applyThm K "aliasSame" (fun Γ ↦ [dv'A Γ, dvA Γ, EA Γ, msA Γ, tysA Γ])
        [hypOr iSame, hypOr (inv₀ 18), hypOr (inv₀ 19), hypOr (inv₀ 20)] <|
      K.conjE <| K.conjE <| fun Γ₁ Φ₁ ψ₁ ↦
      let (iAl, iAlKw, iAlTys) := (Φ₁.length - 4, Φ₁.length - 2, Φ₁.length - 1)
      (at' "the datatype's node" <|
        applyThm K "dataInv" (fun Γ ↦ [dAA Γ, restA Γ, esA Γ, fsA Γ, msA Γ, termsA Γ, namesA Γ,
            numsA Γ, tysA Γ, rA Γ, EA Γ, dv'A Γ, EA Γ])
          ((List.range nInv).map fun k ↦
            stage s!"stepData: the hypothesis {k} at the datatype's node" <|
              if k = 18 then hypOr iAl else if k = 19 then hypOr iAlKw
              else if k = 20 then hypOr iAlTys else hypOr (inv₀ k)) <|
        conjEs K (nInv + 4) fun inv ↦
        dImpE L (inv nInv) (inner inv iWf iSame) (at' "the conclusion" (last K.byHyp)))
        Γ₁ Φ₁ ψ₁
    -- the expansion's step
    let expansion : Deducer := at' "the expansion" <|
      decideIn K (fun Γ ↦ headNamed P (hA Γ) "Datatype.kwData") (K.hypFalse hData) <|
      applyThm K "xpPrefix" (fun Γ ↦ [esA Γ, xpA Γ])
        [stage "stepData: the expansion's run" (K.byHyp (inv₀ 0))] <|
      applyThm K "xpDataDecl" (fun Γ ↦ [xsA Γ, nil, dvA Γ])
        [stage "stepData: the datatypes' keyword" (K.solve 3),
          stage "stepData: the expansion's step" (lastOr K)] <|
      K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
      let (iWf, iStep) := (Φ₂.length - 2, Φ₂.length - 1)
      (normHyps K [iStep] <| at' "the typed forms" <|
        applyThm K "typedFormsApp" (fun Γ ↦ [writtenA Γ, dv'A Γ, esA Γ]) [] <| K.conjE <|
        fun Γ₃ Φ₃ ψ₃ ↦
        let (iFlag, iImp) := (Φ₃.length - 2, Φ₃.length - 1)
        normHyps K [iFlag] (
          dImpE L iImp (stage "stepData: the rest's expansion" (K.byHyp (inv₀ 0))) <|
          last fun iTF ↦ normHyps K [iTF] (block iWf)) Γ₃ Φ₃ ψ₃) Γ₂ Φ₂ ψ₂
    let _ := rA
    let some d := decideIn K (fun Γ ↦ headNamed P (hA Γ) "Datatype.kwGeneric") expansion
        (stage "stepData: a template's instance" (refuteNot K hGen)) a.ctx a.hyps a.concl
      | dbgTrace "stepData: not proved" fun _ ↦ none
    pure (a, d))

end GebTests.Prototypes.FreeTopos.Datatypes

end
