/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeProgramStep
public meta import GebTests.Prototypes.FreeTopos.DatatypeProgramStep -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a constructor's definition at the passes' states

The definition the expansion writes for a constructor of a datatype's declaration is sound at
states of the compiler's passes of which the parts of the invariant of a whole program's
soundness hold ({lit}`Passes.hyps`). The soundness of a constructor's definition at every
context and environment ({lit}`ctorPlain`, {lit}`ctorVar`) is stated under hypotheses on the
reader's and the typing's parts; each is derived here from the invariant's parts, or from the
hypotheses that the definition has a type and that the reader resolves it. The atoms the
definition names are abbreviated by no numeral abbreviation, and the fields' atoms name nothing
but binders: their names are the implementation's, which no definition's name is. The fields'
types cohere with the markers' reading of them where the typing reads them, by the coherence of
the expansion's aliases with the typing environment's abbreviations; the typing reads them
where the definition has a type, and the reader reads the fields' annotations as types where it
resolves the definition. A constructor with a variable field has, within the abstractions over
its fields' binders, that over the variable field's binder, whose annotation is the lists of
the field's type.

## Main definitions

* {lit}`varFieldsT`, {lit}`varTypeT`, {lit}`ctorVarDefT` — the fields' types, the variable
  field's type and the definition's body of a constructor with a variable field.

## Main statements

* {lit}`implAbsent`, {lit}`globAbsent` — a name of the implementation's names no definition.
* {lit}`numOfKws`, {lit}`fieldAllOf` — the numerals read as numbers, and the fields' atoms name
  nothing but binders, at the invariant's parts.
* {lit}`cohOfRead`, {lit}`cohFields` — a field's type the typing reads coheres with the
  marker's reading of it.
* {lit}`fieldsTypedRead`, {lit}`fieldsResolvedRead` — the typing and the reader read each
  field's type where the definition has a type and where the reader resolves it.
* {lit}`ctorSoundAt` — the soundness of a constructor's definition without a variable field.
* {lit}`readTyList`, {lit}`restBinderRead` — the variable field's type, as the typing and the
  reader read it.
* {lit}`ctorSoundVarAt` — the soundness of a constructor's definition with a variable field.

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

/-- A name of the implementation's has no index among names none of which is: by induction on
the names; at a construction, a head equal to the name is the implementation's
({lit}`equalSound`), and the rest's index is absent by the induction hypothesis. In the context
of the names, under the name. -/
def implAbsent (P : Prog) (S : Defs) : Step :=
  ("implAbsent", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let idx (x xs : Term) : Term := pc P "Reader.indexOf" [x, xs]
    -- under the quantifier: the name v0, the names v1
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (S.allL (userPred P) (v 1)) (Internal.Logic.imp o (truth o (implT P (v 0)))
        (notTest o (isSome (idx (v 0) (v 1)))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let base : Deducer := dAllI L <| dImpI L <| dImpI L <| dImpI L (lastFalse K)
    -- a construction: the head v(0), the tail v(1), the name v(2), from the outermost
    let step : Deducer := dAllI L <| dImpI L <| dImpI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let (hAll, hImpl, hIdx) := (Φ₁.length - 3, Φ₁.length - 2, Φ₁.length - 1)
      let (b, tl, nm) := (at_ 0, at_ 1, at_ 2)
      (normHyps K [hAll] <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (iHead, iTail) := (Φ₂.length - 2, Φ₂.length - 1)
        decideIn K (fun Γ ↦ apps equalT [nm Γ, b Γ])
          (decideIn K (fun Γ ↦ isSome (idx (nm Γ) (tl Γ)))
            (stage "implAbsent: no index" (K.hypFalse hIdx))
            (stage "implAbsent: an index in the rest" <| fun Γ Φ ψ ↦
              dAllE L K.G K.E 0 (nm Γ) (K.impE (K.byHyp iTail) <| K.impE (K.byHyp hImpl) <|
                fun Γ Φ ψ ↦ dImpE L (Φ.length - 1) (K.solve 3) (dFalse L dHyp) Γ Φ ψ) Γ Φ ψ))
          (stage "implAbsent: the head" <|
            K.cutThm "equalSound" (fun Γ ↦ [nm Γ]) <| K.allEΓ b <| K.impE (K.solve 3) <|
            normLastK K <|
            fun Γ Φ ψ ↦ dImpE L iHead (K.byHyp hImpl) (dFalse L dHyp) Γ Φ ψ) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    listInduction "implAbsent" φ base step)

/-- A name without an index among the names has no type among the typing environment's
definitions, where the definitions are related to them: a name with a type has an index. In the
context of the name, the names, the environment and the relation's context. -/
def globAbsent (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("globAbsent", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let Γ₀ := [treeTy, list treeTy, T.envTy, Defs3.ctxTy]
    let a : Internal.Thm := ⟨0, Γ₀,
      [T.globT (v 3) (v 2) (v 1), notTest P.o (isSome (pc P "Reader.indexOf" [v 0, v 1]))],
      notTest P.o (isSome (pc P "Typing.lookupName" [v 0, pc P "Typing.envDefs" [v 2]]))⟩
    let nA (Γ : List Tree) : Term := v (Γ.length - Γ₀.length)
    let some d := (dImpI L <| dRwHyp (evalRw K.G K.E [.delta (T.q + 2)] .head) 0 <|
        fun Γ Φ ψ ↦ dAllE L K.G K.E (Φ.length - 1) (nA Γ) (
          K.impE (stage "globAbsent: a type" (K.byHyp 2)) <| K.exE <| K.conjE <|
          fun Γ Φ ψ ↦ normHyps K [Φ.length - 2] (
            dImpE L 1 (stage "globAbsent: an index" (K.solve 3)) (dFalse L dHyp)) Γ Φ ψ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "globAbsent: not proved" fun _ ↦ none
    pure (a, d))

/-- The writer's numerals read as numbers ({name}`numT`) at numeral abbreviations coherent with
the keywords, where the digits of a tree's label read as its leaf ({name}`decRoundT`) and are
fixed by the abbreviations' expansion ({name}`digitsFixedT`): a numeral's name is abbreviated by
none, being a numeral's. In the context of the numeral abbreviations. -/
def numOfKws (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("numOfKws", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let a : Internal.Thm := ⟨0, [list treeTy], [T.kwsT (v 0), decRoundT P, digitsFixedT P],
      numT P (v 0)⟩
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (numsA, nA) := (at_ 0, at_ 1)
    let xA (Γ : List Tree) : Term := atomNameT (pc P "Recognize.num" [nA Γ])
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let reserved (Γ : List Tree) : Term :=
      isSome (pc P "Reader.indexOf" [xA Γ, pc P "Reader.reservedNames" []])
    let impl (Γ : List Tree) : Term := pc P "implName" [xA Γ]
    -- the numeral's name excluded from the abbreviated names: it is a numeral's
    let excluded : Deducer := fun Γ Φ ψ ↦
      dAllE L K.G K.E 1 (nA Γ) (normLastK K <|
        decideIn K reserved (decideIn K impl (K.solve 3) (K.solve 3)) (K.solve 3)) Γ Φ ψ
    let plain : Deducer := dImpI L <| last fun iAb ↦
      dRwHyp (evalRw K.G K.E [.delta (T.q + 5 + 2 * nFolds)] .head) 0 <|
      K.allEΓ xA <| K.impE (stage "numOfKws: abbreviated" (K.byHyp iAb)) <|
      K.impE (stage "numOfKws: a numeral's name" excluded) <| lastFalse K
    let some d := (dAllI L <| dConjI L plain <| dConjI L
        (stage "numOfKws: the digits read" fun Γ Φ ψ ↦ dAllE L K.G K.E 1 (nA Γ) dHyp Γ Φ ψ)
        (stage "numOfKws: the digits fixed" fun Γ Φ ψ ↦
          dAllE L K.G K.E 2 (numsA Γ) (K.allEΓ nA dHyp) Γ Φ ψ)) a.ctx a.hyps a.concl
      | dbgTrace "numOfKws: not proved" fun _ ↦ none
    pure (a, d))

/-- The atoms of a constructor's fields name nothing but binders ({name}`fieldAllT`), where the
numeral abbreviations are coherent with the keywords, the numerals read as numbers, the
definitions are related to the typing environment's and no name is one of the implementation's:
a field's atom, whose name is the implementation's, is abbreviated by none; its number's digits
are fixed; its name has no index among the names ({name}`implAbsent`), so no type among the
environment's definitions ({name}`globAbsent`), and none among the primitives' names, none of
which is the implementation's; and it is not the unit value's keyword, whose name does not
begin as the implementation's ({name}`fieldNameHead`). In the context of the names, the numeral
abbreviations, the typing environment and the relation's context. -/
def fieldAllOf (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("fieldAllOf", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let Γ₀ := [list treeTy, list treeTy, T.envTy, Defs3.ctxTy]
    let (names, nums, Ev, R) := (v 0, v 1, v 2, v 3)
    let a : Internal.Thm := ⟨0, Γ₀,
      [T.kwsT nums, numT P nums, T.globT R Ev names, S.allL (userPred P) names],
      fieldAllT P Ev nums⟩
    let (hKws, hNum, hGlob, hUser) := (0, 1, 2, 3)
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (RA, EA, namesA, kA) := (at_ 0, at_ 1, at_ 3, at_ 4)
    let nmA (Γ : List Tree) : Term := atomNameT (fieldAtomT P (kA Γ))
    let prims := pc P "Reader.primNames" []
    let kwUnit := pc P "Reader.kwUnitValue" []
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let at' (m : String) (k : Deducer) : Deducer := stage s!"fieldAllOf: {m}" k
    -- no name of a closed list is the implementation's: each conjunct's test refuted
    let noImpl : Deducer := Nat.rec (motive := fun _ ↦ Deducer) (K.solve 1) (fun _ rec Γ Φ ψ ↦
      (K.solve 1 Γ Φ ψ).orElse fun _ ↦
        K.norm (dConjI L (dImpI L (lastFalse K)) rec) Γ Φ ψ) 96
    -- the name without an index among names none of which is the implementation's
    let absent (xs : List Tree → Term) (none : Deducer) (k : Deducer) : Deducer :=
      K.cutThm "implAbsent" (fun Γ ↦ [xs Γ]) <| K.allEΓ nmA <| K.impE none <|
      K.impE (at' "the name the implementation's" (K.solve 3)) k
    let reserved (Γ : List Tree) : Term :=
      isSome (pc P "Reader.indexOf" [nmA Γ, pc P "Reader.reservedNames" []])
    let plain : Deducer := dImpI L <| last fun iAb ↦
      dRwHyp (evalRw K.G K.E [.delta (T.q + 5 + 2 * nFolds)] .head) hKws <|
      K.allEΓ nmA <| K.impE (at' "abbreviated" (K.byHyp iAb)) <|
      K.impE (at' "the implementation's name" (decideIn K reserved (K.solve 3) (K.solve 3))) <|
      lastFalse K
    let fixed : Deducer := fun Γ Φ ψ ↦
      dAllE L K.G K.E hNum (kA Γ) (K.conjE <| K.conjE <| last K.byHyp) Γ Φ ψ
    let noDef : Deducer := absent namesA (at' "the names" (hypOrK K hUser)) <| last fun iIdx ↦
      applyThm K "globAbsent" (fun Γ ↦ [nmA Γ, namesA Γ, EA Γ, RA Γ])
        [at' "related" (hypOrK K hGlob), at' "no index" (K.byHyp iIdx)] (last K.byHyp)
    let noPrim : Deducer := absent (fun _ ↦ prims) (at' "the primitives' names" noImpl) <|
      last K.byHyp
    let noUnit : Deducer := dImpI L <| last fun iNamed ↦
      applyThm K "fieldNameHead" (fun Γ ↦ [kwUnit, kA Γ])
        [at' "named as the unit value" (K.byHyp iNamed)] (lastFalse K)
    let some d := (dAllI L <| dConjI L (at' "plain" plain) <| dConjI L (at' "fixed" fixed) <|
        dConjI L (at' "no definition" noDef) <| dConjI L (at' "no primitive" noPrim)
          (at' "no unit value" noUnit)) a.ctx a.hyps a.concl
      | dbgTrace "fieldAllOf: not proved" fun _ ↦ none
    pure (a, d))

/-- A formula proved by a deducer and cut in, used as a hypothesis after the hypotheses. -/
def cutBy (ψ : List Tree → Term) (prove k : Deducer) : Deducer := fun Γ Φ φ ↦
  (prove Γ Φ (ψ Γ)).bind fun d ↦ dCut (ψ Γ) d k Γ Φ φ

/-- Trees with equal quotations are equal: the quotations' trees, read back, are the trees. In
the context of the trees. -/
def quoteInj (P : Prog) (S : Defs) : Step :=
  ("quoteInj", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let back (t : Term) : Term := pc P "Prelude.get" [pc P "Eval.unquote" [quoteV P t]]
    let a : Internal.Thm := ⟨0, [treeTy, treeTy], [Term.eq (quoteV P (v 1)) (quoteV P (v 0))],
      Term.eq (v 1) (v 0)⟩
    let some d := (cutBy (fun _ ↦ Term.eq (back (v 1)) (back (v 0)))
        (dRwBy (evalRw K.G K.E [.hyp 0] .full) K.byNorm) (normLastK K dHyp))
        a.ctx a.hyps a.concl
      | dbgTrace "quoteInj: not proved" fun _ ↦ none
    pure (a, d))

/-- A tree whose quotation is related at a datatype is a member of it: the relation unfolded at
the datatype, a variable, gives a member with the same quotation, the tree
({name}`quoteInj`). In the context of the tree, the datatype's name and the relation's
context. -/
def relDataElim (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relDataElim", fun ix E ↦ do
    let K₀ := ctorKit P S T ix E
    let rebuilding := relRebuildNames.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size
    let K : Kit := { K₀ with more := K₀.more ++ rebuilding }
    let (t, n, R) := (v 0, v 1, v 2)
    let a : Internal.Thm := ⟨0, [treeTy, treeTy, Defs3.ctxTy],
      [Term.app (T.relT R (pc P "Typing.tyData" [n])) (quoteV P t)],
      truth P.o (pc P "Typing.memberOf" [Term.snd R,
        nodeT (Term.pair (numeral 1) (call D.children [] [n])), t])⟩
    let some d := (fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ [.delta T.q]) .full) 0
          (K.exE <| K.conjE <| fun Γ₁ Φ₁ ψ₁ ↦
          let iM := Φ₁.length - 1
          (applyThm K "quoteInj" (fun Γ ↦ [v (Γ.length - Γ₁.length), v (Γ.length - 1 - 2)])
            [stage "relDataElim: the quotations" K.byNorm] <| normLastK K <|
            stage "relDataElim: the member" (K.byHyp iM)) Γ₁ Φ₁ ψ₁) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "relDataElim: not proved" fun _ ↦ none
    pure (a, d))

/-- A field's type coheres with the marker's reading of it ({name}`cohT`) where the typing reads
it: the expansion of its aliases no marker's datatype's atom, the marker's test holds of any
tree; else the typing reads it as that datatype ({name}`cohAt`), at which the relation is
membership in it ({name}`relDataElim`), the marker's test. In the context of the type, the
typing environment, the declarations and the relation's context. -/
def cohOfRead (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cohOfRead", fun ix E ↦ do
    let K₀ := ctorKit P S T ix E
    let rebuilding := relRebuildNames.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size
    let K : Kit := { K₀ with more := K₀.more ++ rebuilding }
    let L := K.L
    let o := P.o
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let Γ₀ := [treeTy, T.envTy, list treeTy, Defs3.ctxTy]
    let (F, Ev, dv, R) := (v 0, v 1, v 2, v 3)
    let ms := Term.snd R
    let a : Internal.Thm := ⟨0, Γ₀,
      [aliasT P dv Ev ms, aliasKwT P dv, markerNamesT P ms, noSortsT P Ev,
        truth o (isSome (pc P "Typing.readTy" [Ev, rawT T Ev F]))],
      cohT P T R Ev dv F⟩
    let hMarkers := 2
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (RA, dvA, EA, FA, tA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4)
    let msA (Γ : List Tree) : Term := Term.snd (RA Γ)
    let XA (Γ : List Tree) : Term := pc P "Datatype.expandAliases" [dvA Γ, FA Γ]
    let marked (Γ : List Tree) : Term :=
      isSome (pc P "Reader.indexOf" [XA Γ, pc P "Typing.markerNames" [msA Γ]])
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let at' (m : String) (k : Deducer) : Deducer := stage s!"cohOfRead: {m}" k
    let testing (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta (P.idx "Typing.fieldOk")]) .full) k Γ Φ ψ
    let some d := (dAllI L <| dImpI L <| last fun hRel ↦
        decideIn K marked (at' "no marker's datatype" (testing (K.solve 3))) <|
        at' "a marker's datatype" <|
        applyThm K "cohAt" (fun Γ ↦ [FA Γ, msA Γ, EA Γ, dvA Γ])
          ((List.range 5).map (fun i ↦ at' s!"the hypothesis {i}" (hypOrK K i)) ++
            [at' "the expansion a marker's" (K.solve 3)]) <| normLastK K <|
        -- the relation at the datatype: membership; the datatype's atom a marker's name, an
        -- atom
        applyThm K "relDataElim" (fun Γ ↦ [tA Γ, atomNameT (XA Γ), RA Γ])
          [at' "related at the datatype" (K.byHyp hRel)] <| last fun iM ↦
        fun Γ Φ ψ ↦ dAllE L K.G K.E hMarkers (XA Γ) (
          K.impE (at' "the marker's name" (K.solve 3)) <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
          let iAtom := Φ₂.length - 2
          (applyThm K "atomNode" (fun Γ ↦ [XA Γ]) [at' "an atom" (K.byHyp iAtom)] <|
            normLastK K <| at' "the member" (testing (K.byHyp iM))) Γ₂ Φ₂ ψ₂) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "cohOfRead: not proved" fun _ ↦ none
    let _ := (F, Ev, dv)
    pure (a, d))

/-- The typing of the abstractions over the binders of a constructor's fields around a form
reads each field's type, and types the form in some context: by induction on the fields; at a
field before others the abstraction over its binder is typed ({lit}`lamTypedOne`), so its
annotation reads, and those over the others' binders are typed in the context extended. In the
context of the fields, under the form, the number of the fields, the typing environment and
the context. -/
def fieldsTypedRead (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("fieldsTypedRead", fun ix E ↦ do
    let K := lamKit P S T ix E
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let subT := (primT Kernel.Prim.sub).getD Term.star
    let read (Ev F : Term) : Term := pc P "Typing.readTy" [Ev, rawT T Ev F]
    let syn (Ev cx fs nf x : Term) : Term :=
      pc P "Typing.synIn" [Ev, cx, nestT P (binderFold P nf fs) x]
    let pred (Ev : Term) : Term := Term.lam treeTy (truth o (isSome (read (sh 1 Ev) (v 0))))
    -- under the quantifiers: the context v0, the environment v1, the number v2, the form v3,
    -- the fields v4
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.all o treeTy
      (Term.lam treeTy (Internal.Logic.all o T.envTy (Term.lam T.envTy (Internal.Logic.all o Ls
        (Term.lam Ls (Internal.Logic.imp o (truth o (isSome (syn (v 1) (v 0) (v 4) (v 2) (v 3))))
          (Internal.Logic.conj o (S.allL (pred (v 1)) (v 4))
            (Internal.Logic.ex o Ls (Term.lam Ls
              (truth o (isSome (pc P "Typing.synIn" [v 2, v 0, v 4]))))))))))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let intro (k : Deducer) : Deducer := dAllI L <| dAllI L <| dAllI L <| dAllI L <| dImpI L k
    let base : Deducer := intro <| last fun hSyn ↦ dConjI L (K.solve 3) fun Γ Φ ψ ↦
      dExI L K.G K.E (at_ 3 Γ) (stage "fieldsTypedRead: the form typed" (K.byHyp hSyn)) Γ Φ ψ
    -- a construction: the field v(0), the others v(1), then the form, the number, the
    -- environment and the context
    let step : Deducer := intro <| last fun hSyn ↦ fun Γ₁ Φ₁ ψ₁ ↦
      let (FA, fsA, xA, nfA, EA, cxA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5)
      -- the count of the fields after, the field's atom and the abstractions over the others
      let acc (Γ : List Tree) : Term :=
        (binderFold P (nfA Γ) (fsA Γ)).children.headD Term.star
      let aA (Γ : List Tree) : Term := fieldAtomT P
        (apps subT [apps subT [nfA Γ, leafT (numeral 1)], Term.fst (acc Γ)])
      let restA (Γ : List Tree) : Term := nestT P (binderFold P (nfA Γ) (fsA Γ)) (xA Γ)
      let entry (Γ : List Tree) : Term := pc P "Typing.abbr"
        [pc P "Typing.atomName" [rawT T (EA Γ) (aA Γ)], get (read (EA Γ) (FA Γ))]
      (applyThm K "lamTypedOne" (fun Γ ↦ [restA Γ, FA Γ, aA Γ, cxA Γ, EA Γ])
        [stage "fieldsTypedRead: the abstraction typed" (K.byHyp hSyn)] <|
        K.conjE <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (iRead, iBody) := (Φ₂.length - 4, Φ₂.length - 2)
        -- the induction hypothesis at the context extended: the others' types and the form
        let ih (k : Deducer) : Deducer := fun Γ Φ ψ ↦
          dAllE L K.G K.E 0 (xA Γ) (K.allEΓ nfA <| K.allEΓ EA <|
            K.allEΓ (fun Γ ↦ consT treeTy (entry Γ) (cxA Γ)) <|
            K.impE (K.byHyp iBody) <| K.conjE k) Γ Φ ψ
        K.norm (dConjI L
          (dConjI L (stage "fieldsTypedRead: the field's type" (K.byHyp iRead))
            (stage "fieldsTypedRead: the others"
              (ih fun Γ Φ ψ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ)))
          (stage "fieldsTypedRead: the form typed" (ih (last K.byHyp)))) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    listInduction "fieldsTypedRead" φ base step)

/-- An equation proved by a hypothesis equal to it once both are normalized, without the
hypothesis among the rules. -/
def eqByHyp (K : Kit) (h : ℕ) : Deducer := fun Γ Φ ψ ↦
  dRwBy (evalRw K.G K.E (K.rulesEx Φ h) .full)
    (dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h dHyp) Γ Φ ψ

/-- The fields' types cohere with the marker's reading of them ({name}`cohT`) where the typing
reads each ({name}`cohOfRead`): by induction on the fields. In the context of the fields, under
the relation's context, the declarations and the typing environment. -/
def cohFields (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cohFields", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let imp := Internal.Logic.imp o
    let R := Defs3.ctxTy
    let Ls := list treeTy
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    -- under the quantifiers: the environment v0, the declarations v1, the relation's context
    -- v2, the fields v3
    let (Ev, dv, Rc, fs) := (v 0, v 1, v 2, v 3)
    let ms := Term.snd Rc
    let readPred := Term.lam treeTy
      (truth o (isSome (pc P "Typing.readTy" [sh 1 Ev, rawT T (sh 1 Ev) (v 0)])))
    let cohPred := Term.lam treeTy (cohT P T (sh 1 Rc) (sh 1 Ev) (sh 1 dv) (v 0))
    let φ := Internal.Logic.all o R (Term.lam R (Internal.Logic.all o Ls (Term.lam Ls
      (Internal.Logic.all o T.envTy (Term.lam T.envTy (imp (aliasT P dv Ev ms) (imp (aliasKwT P dv)
        (imp (markerNamesT P ms) (imp (noSortsT P Ev)
          (imp (S.allL readPred fs) (S.allL cohPred fs)))))))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let intro (k : Deducer) : Deducer := repeatK 3 (dAllI L) (repeatK 5 (dImpI L) k)
    let base : Deducer := intro (K.solve 3)
    -- a construction: the field v(0), the others v(1), then the relation's context, the
    -- declarations and the environment
    let step : Deducer := intro fun Γ₁ Φ₁ ψ₁ ↦
      let h (k : ℕ) : ℕ := Φ₁.length - 5 + k
      let (FA, RA, dvA, EA) := (at_ 0, at_ 2, at_ 3, at_ 4)
      (normHyps K [h 4] <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (iHead, iTail) := (Φ₂.length - 2, Φ₂.length - 1)
        K.norm (dConjI L
          (stage "cohFields: the field" <|
            applyThm K "cohOfRead" (fun Γ ↦ [FA Γ, EA Γ, dvA Γ, RA Γ])
              ((List.range 4).map (fun k ↦ hypOrK K (h k)) ++ [K.byHyp iHead]) <|
            last K.byHyp)
          (stage "cohFields: the others" fun Γ Φ ψ ↦
            dAllE L K.G K.E 0 (RA Γ) (K.allEΓ dvA <| K.allEΓ EA <| last fun hI ↦
              impEs L hI ((List.range 4).map (fun k ↦ hypOrK K (h k)) ++
                [K.byHyp iTail]) <| last K.byHyp) Γ Φ ψ)) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    listInduction "cohFields" φ base step)

/-- An abbreviation's lookup, where it finds one, is the option of what it finds: by induction
on the abbreviations. In the context of the abbreviations, under the name. -/
def lookupAbbrevSome (P : Prog) (S : Defs) : Step :=
  ("lookupAbbrevSome", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, numsEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let childT ← primT Kernel.Prim.child
    let look (n xs : Term) : Term := pc P "Reader.lookupAbbrev" [n, xs]
    let whole (t : Term) : Term := Term.eq t (pc P "Prelude.some" [pc P "Prelude.get" [t]])
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (truth o (pc P "Prelude.isSome" [look (v 0) (v 1)])) (whole (look (v 0) (v 1)))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let base : Deducer := dAllI L <| dImpI L (lastFalse K)
    -- a construction: the head v(0), the tail v(1), the name v(2)
    let step : Deducer := dAllI L <| dImpI L <| last fun hSome ↦
      decideIn K (fun Γ ↦ apps equalT [at_ 2 Γ, apps childT [at_ 0 Γ, leafT bnilT]])
        (stage "lookupAbbrevSome: among the rest" fun Γ Φ ψ ↦
          dAllE L K.G K.E 0 (at_ 2 Γ) (K.impE (K.byHyp hSome) <| last (eqByHyp K)) Γ Φ ψ)
        (stage "lookupAbbrevSome: the head" K.byNorm)
    listInduction "lookupAbbrevSome" φ base step)

/-- The reader's reading of a type, where it reads one, is the option of the type read: the form
a node, each of the reading's tests split; a type read is an option written, or an
abbreviation's lookup ({name}`lookupAbbrevSome`). In the context of the form and the type
abbreviations. -/
def readTypeSome (P : Prog) (S : Defs) : Step :=
  ("readTypeSome", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let read (tys e : Term) : Term := pc P "Reader.readType" [tys, e]
    let whole (t : Term) : Term := Term.eq t (pc P "Prelude.some" [pc P "Prelude.get" [t]])
    let a : Internal.Thm := ⟨0, [treeTy, list treeTy],
      [truth P.o (pc P "Prelude.isSome" [read (v 1) (v 0)])], whole (read (v 1) (v 0))⟩
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    -- an abbreviation's lookup, the reading's normal form: an application to the name and the
    -- abbreviations
    let lookup : Deducer := fun Γ Φ ψ ↦
      let t := read (v (Γ.length - 1)) (v (Γ.length - 2))
      match (evalRw K.G K.E (K.rules Φ) .full Γ Φ t).map (·.1) with
      | some r => match r.label, r.children with
        | .app, [f, xs] => match f.label, f.children with
          | .app, [_, n] =>
            (K.cutThm "lookupAbbrevSome" (fun _ ↦ [xs]) <| K.allEΓ (fun _ ↦ n) <|
              K.impE (K.byHyp 0) <| last (eqByHyp K)) Γ Φ ψ
          | _, _ => none
        | _, _ => none
      | none => none
    let close : Deducer := fun Γ Φ ψ ↦
      (K.hypFalse 0 Γ Φ ψ).orElse fun _ ↦ (K.byNorm Γ Φ ψ).orElse fun _ ↦ lookup Γ Φ ψ
    let some d := (K.treeNode (v 0) fun Γ₁ Φ₁ ψ₁ ↦
        splitCond K Γ₁.length (read (v 3) (v 2)) 32
          (stage "readTypeSome: a reading" close) Γ₁ Φ₁ ψ₁) a.ctx a.hyps a.concl
      | dbgTrace "readTypeSome: not proved" fun _ ↦ none
    pure (a, d))

/-- The reader's resolution of an abstraction reads its binders: where it does not, the
abstraction has no resolution. In the context of the binders, the body, the scope, the type
abbreviations, the definitions' names and the numeral abbreviations. -/
def lamBindersRead (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("lamBindersRead", fun ix E ↦ do
    let K := denKit P S ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let Γ₀ := [treeTy, treeTy, Ls, Ls, Ls, Ls]
    let rLam := pc P "Recognize.rLam" []
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let abbr (nums : Term) : Term := isSome (pc P "Reader.lookupAbbrev" [atomNameT rLam, nums])
    let bindersOf (tys nums b : Term) : Term := pc P "Reader.readBinders" [tys,
      pc P "Reader.binders" [pc P "Reader.expandNums" [nums, b]]]
    let (b, e, scope, tys, names, nums) := (v 0, v 1, v 2, v 3, v 4, v 5)
    let thm : Internal.Thm := ⟨0, Γ₀,
      [notTest o (abbr nums), truth o (isSome (pc P "Reader.resolve" [tys, names,
        pc P "Reader.expandNums" [nums, pc P "Recognize.s3" [rLam, b, e]], scope]))],
      truth o (isSome (bindersOf tys nums b))⟩
    let (numsA, tysA, bA) := (atPos 0, atPos 2, atPos 5)
    let unfold := resolveRules P T ix E ++ [.delta (T.argIdx 3)]
    let main : Deducer :=
      decideIn K (fun Γ ↦ abbr (numsA Γ))
        (decideOpt K (fun Γ ↦ bindersOf (tysA Γ) (numsA Γ) (bA Γ))
          (linkK K "lamBindersRead: no binders" fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ 1 ++ unfold) .full) 1 (dFalse L dHyp) Γ Φ ψ)
          (linkK K "lamBindersRead: binders" (K.solve 3)))
        (dImpE L 0 (K.solve 3) fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)
    let _ := (e, scope, names)
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "lamBindersRead: not proved" fun _ ↦ none
    pure (thm, d))

/-- The reader's reading of one binder, an atom named by no abbreviation whose characters the
expansion of the numeral abbreviations fixes, reads its annotation as a type: where it does
not, the binders do not read. In the context of the atom's characters, the annotation, the
numeral abbreviations and the type abbreviations. -/
def binderTypeRead (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("binderTypeRead", fun ix E ↦ do
    let K := denKit P S ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let Γ₀ := [Ls, treeTy, Ls, Ls]
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let atom (cs : Term) : Term := nodeT (Term.pair (numeral 1) cs)
    let abbr (cs nums : Term) : Term :=
      isSome (pc P "Reader.lookupAbbrev" [atomNameT (atom cs), nums])
    let read (tys nums F : Term) : Term :=
      pc P "Reader.readType" [tys, pc P "Reader.expandNums" [nums, F]]
    let (cs, F, nums, tys) := (v 0, v 1, v 2, v 3)
    let fn := Term.lam treeTy (pc P "Reader.expandNums" [sh 1 nums, v 0])
    let thm : Internal.Thm := ⟨0, Γ₀,
      [notTest o (abbr cs nums), truth o (pc P "charsFixed" [fn, cs]),
        truth o (isSome (pc P "Reader.readBinders" [tys, pc P "Reader.binders"
          [pc P "Reader.expandNums" [nums, listNode [listNode [atom cs, F]]]]]))],
      truth o (isSome (read tys nums F))⟩
    let (tysA, numsA, FA, csA) := (atPos 0, atPos 1, atPos 2, atPos 3)
    let unfold := resolveRules P T ix E ++ [.delta (T.argIdx 3)]
    let main : Deducer :=
      decideIn K (fun Γ ↦ abbr (csA Γ) (numsA Γ))
        (K.cutThm "charsFixedEq" (fun Γ ↦ [csA Γ, numsA Γ]) <| K.impE (K.byHyp 1) <|
          normLastK K <|
          (decideOpt K (fun Γ ↦ read (tysA Γ) (numsA Γ) (FA Γ))
            (linkK K "binderTypeRead: no type" fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ 2 ++ unfold) .full) 2 (dFalse L dHyp) Γ Φ ψ)
            (linkK K "binderTypeRead: a type" (K.solve 3))))
        (dImpE L 0 (K.solve 3) fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "binderTypeRead: not proved" fun _ ↦ none
    pure (thm, d))

/-- The reader's resolution of the abstractions over the binders of a constructor's fields
around a form reads each field's annotation as a type ({name}`readOkT`), and resolves the
form in some scope: by induction on the fields; at a field before others the abstraction over
its binder, which no keyword of the erasure names ({lit}`fieldNameHead`), resolves, so its
binders read ({name}`lamBindersRead`) and its annotation reads ({name}`binderTypeRead`), as
the option of a type ({name}`readTypeSome`), and the abstractions over the others' binders
resolve in the scope extended ({lit}`readBinderOne`, {lit}`lamRead`). In the context of the
fields, under the form, the number of the fields, the typing environment, the numeral
abbreviations, the type abbreviations, the definitions' names and the scope. -/
def fieldsResolvedRead (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("fieldsResolvedRead", fun ix E ↦ do
    let K := lamKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let imp := Internal.Logic.imp o
    let all := Internal.Logic.all o
    let Ls := list treeTy
    let subT := (primT Kernel.Prim.sub).getD Term.star
    let rLam := pc P "Recognize.rLam" []
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let er (t : Term) : Term := pc P "Datatype.eraseExpr" [t]
    let res (tys names nums t scope : Term) : Term :=
      pc P "Reader.resolve" [tys, names, pc P "Reader.expandNums" [nums, t], scope]
    -- under the quantifiers: the scope v0, the names v1, the type abbreviations v2, the numeral
    -- abbreviations v3, the environment v4, the number v5, the form v6, the fields v7
    let (scope, names, tys, nums, Ev, nf, x, fs) := (v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7)
    let readPred := Term.lam treeTy (readOkT P (sh 1 nums) (sh 1 tys) (v 0))
    let φ := [treeTy, treeTy, T.envTy, Ls, Ls, Ls, Ls].foldr (fun A b ↦ all A (Term.lam A b))
      (imp (fieldAllT P Ev nums)
        (imp (notTest o (isSome (pc P "Reader.lookupAbbrev" [atomNameT rLam, nums])))
          (imp (truth o (isSome (res tys names nums
              (er (nestT P (binderFold P nf fs) x)) scope)))
            (Internal.Logic.conj o (S.allL readPred fs)
              (Internal.Logic.ex o Ls (Term.lam Ls (truth o (isSome
                (res (sh 1 tys) (sh 1 names) (sh 1 nums) (er (sh 1 x)) (v 0))))))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let intro (k : Deducer) : Deducer := repeatK 7 (dAllI L) (repeatK 3 (dImpI L) k)
    let base : Deducer := intro <| last fun hRes ↦ dConjI L (K.solve 3) fun Γ Φ ψ ↦
      dExI L K.G K.E (at_ 6 Γ) (stage "fieldsResolvedRead: the form resolved" (K.byHyp hRes))
        Γ Φ ψ
    -- a construction: the field v(0), the others v(1), then the form, the number, the
    -- environment, the abbreviations, the names and the scope; after the induction hypothesis
    -- the atoms' properties, the keyword's and the resolution
    let step : Deducer := intro fun Γ₁ Φ₁ ψ₁ ↦
      let (hField, hLam, hRes) := (Φ₁.length - 3, Φ₁.length - 2, Φ₁.length - 1)
      let (FA, fsA, xA, nfA, EA, numsA, tysA, namesA, scopeA) :=
        (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5, at_ 6, at_ 7, at_ 8)
      let acc (Γ : List Tree) : Term :=
        (binderFold P (nfA Γ) (fsA Γ)).children.headD Term.star
      let kA (Γ : List Tree) : Term :=
        apps subT [apps subT [nfA Γ, leafT (numeral 1)], Term.fst (acc Γ)]
      let aA (Γ : List Tree) : Term := fieldAtomT P (kA Γ)
      let restA (Γ : List Tree) : Term := nestT P (binderFold P (nfA Γ) (fsA Γ)) (xA Γ)
      let readA (Γ : List Tree) : Term := pc P "Reader.readType" [tysA Γ,
        pc P "Reader.expandNums" [numsA Γ, er (FA Γ)]]
      let binderA (Γ : List Tree) : Term := listNode [listNode [aA Γ, er (FA Γ)]]
      let typeA (Γ : List Tree) : Term := pc P "Prelude.get" [readA Γ]
      -- no keyword of the erasure names the binder
      let notName (kw : String) : Deducer := dImpI L <|
        applyThm K "fieldNameHead" (fun Γ ↦ [pc P kw [], kA Γ]) [last K.byHyp] (lastFalse K)
      -- a hypothesis and the goal, rewritten by equations alone
      let bits := [D.bnil, D.b0, D.b1].map Internal.NormRule.delta
      let raw₁ : List Internal.NormRule := Translation.baseRules ++ bits
      let rawHyp (rs : List Internal.NormRule) (h : ℕ) : Deducer :=
        dRwHyp (evalRw K.G K.E rs .full) h <| dRwBy (evalRw K.G K.E rs .full) dHyp
      (fun Γ Φ ψ ↦ dAllE L K.G K.E hField (kA Γ)
        (stage "fieldsResolvedRead: the atom's parts" <|
        K.conjE <| K.conjE <| K.conjE <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (hPl, hFx) := (Φ₂.length - 8, Φ₂.length - 6)
        let fixed : Deducer := stage "fieldsResolvedRead: fixed" (applyThm K "fixedField"
          (fun Γ ↦ [pc P "Typing.decimalChars" [kA Γ], numsA Γ]) [K.byHyp hFx] (last K.byHyp))
        (applyThm K "eraseLam" (fun Γ ↦ [restA Γ, FA Γ, fieldChars P (kA Γ)])
            (binderKws.map fun kw ↦ stage s!"fieldsResolvedRead: named {kw}" (notName kw)) <|
          stage "fieldsResolvedRead: the erasure's equation" <|
          last fun hEr₀ ↦ dRwHyp (evalRw K.G K.E raw₁ .full) hEr₀ <| last fun hEr ↦
          let raw₂ := raw₁ ++ [.hyp hEr]
          stage "fieldsResolvedRead: the binders" <|
          applyThm K "lamBindersRead" (fun Γ ↦ [binderA Γ, er (restA Γ), scopeA Γ, tysA Γ,
              namesA Γ, numsA Γ])
            [stage "fieldsResolvedRead: the keyword" (hypOrK K hLam),
              stage "fieldsResolvedRead: the abstraction resolved" (rawHyp raw₂ hRes)] <|
          last fun hBs ↦
          applyThm K "binderTypeRead" (fun Γ ↦ [fieldChars P (kA Γ), er (FA Γ), numsA Γ,
              tysA Γ])
            [stage "fieldsResolvedRead: not abbreviated" (K.byHyp hPl), fixed,
              stage "fieldsResolvedRead: the binders read" (hypOrK K hBs)] <|
          last fun hRead ↦
          applyThm K "readTypeSome" (fun Γ ↦ [pc P "Reader.expandNums" [numsA Γ, er (FA Γ)],
              tysA Γ]) [stage "fieldsResolvedRead: a type read" (hypOrK K hRead)] <|
          last fun hEq ↦
          applyThm K "readBinderOne" (fun Γ ↦ [typeA Γ, er (FA Γ), fieldChars P (kA Γ),
              numsA Γ, tysA Γ])
            [stage "fieldsResolvedRead: not abbreviated" (K.byHyp hPl), fixed,
              stage "fieldsResolvedRead: the type" fun Γ Φ ψ ↦
                (dHyp Γ Φ ψ).orElse fun _ ↦ eqByHyp K hEq Γ Φ ψ] <| last fun hBsEq ↦
          applyThm K "lamRead" (fun Γ ↦ [atomNameT (aA Γ), typeA Γ, er (restA Γ), binderA Γ,
              nilT treeTy, scopeA Γ, tysA Γ, namesA Γ, numsA Γ,
              Term.pair (nilT treeTy) (nilT treeTy)])
            [stage "fieldsResolvedRead: the keyword" (hypOrK K hLam),
              stage "fieldsResolvedRead: the binders' reading" (hypOrK K hBsEq),
              stage "fieldsResolvedRead: the abstraction resolved" (rawHyp raw₂ hRes)] <|
          last fun hBody ↦
          -- the induction hypothesis at the scope extended: the others' types and the form
          let ih (k : Deducer) : Deducer := fun Γ Φ ψ ↦
            dAllE L K.G K.E 0 (xA Γ) (K.allEΓ nfA <| K.allEΓ EA <| K.allEΓ numsA <|
              K.allEΓ tysA <| K.allEΓ namesA <|
              K.allEΓ (fun Γ ↦ consT treeTy (atomNameT (aA Γ)) (scopeA Γ)) <|
              last fun hI ↦ impEs L hI [hypOrK K hField, hypOrK K hLam, K.byHyp hBody] <|
              K.conjE k) Γ Φ ψ
          stage "fieldsResolvedRead: both" <| K.norm (dConjI L
            (dConjI L (stage "fieldsResolvedRead: the field's type" fun Γ Φ ψ ↦
                dExI L K.G K.E (typeA Γ) (eqByHyp K hEq) Γ Φ ψ)
              (stage "fieldsResolvedRead: the others"
                (ih fun Γ Φ ψ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ)))
            (stage "fieldsResolvedRead: the form resolved" (ih (last K.byHyp))))) Γ₂ Φ₂ ψ₂)
        Γ Φ ψ) Γ₁ Φ₁ ψ₁
    listInduction "fieldsResolvedRead" φ base step)

/-- The names of the atoms the constructors' soundness assumes abbreviated by no numeral
abbreviation: those of the list's construction, the node, the abstraction, the empty list and
the trees' type. -/
def ctorAtoms (P : Prog) : List Term :=
  ["Recognize.rCons", "Recognize.rNode", "Recognize.rLam", "Recognize.rNil", "Recognize.rT"].map
    fun a ↦ atomNameT (pc P a [])

/-- The names of the lemmas that the constructors' atoms' names are excluded from the
abbreviated names, with the names. -/
def ctorExcludedNames (P : Prog) : List (Term × String) :=
  (ctorAtoms P).zipIdx.map fun (n, i) ↦ (n, s!"ctorExcluded{i}")

/-- The node's name is a primitive's: closed, by normalization of the presence of its index
among the primitives' names ({name}`isSomeIndexOfCons`, {name}`truthOfEq`), the left disjunct
of the test the reader's names exclude. -/
def nodePrimitive (P : Prog) (S : Defs) : Step :=
  ("nodePrimitive", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, ["isSomeIndexOfCons", "indexOfNil"]⟩
    let equalT ← primT Kernel.Prim.equal
    let n := atomNameT (pc P "Recognize.rNode" [])
    let prim := pc P "Prelude.isSome" [pc P "Reader.indexOf" [n, pc P "Reader.primNames" []]]
    let unit := apps equalT [n, pc P "Reader.kwUnitValue" []]
    let φ := truth P.o (pc P "Prelude.or" [prim, unit])
    let byTest : Deducer := applyThm K "truthOfEq" (fun _ ↦ [prim]) [fun Γ Φ ψ ↦
        dEq (fun Γ _ t u ↦ byMode .full K.G K.E 0 (K.rules []) Γ [] t u) Γ Φ ψ] dHyp
    let some d := (applyThm K "orLeftT" (fun _ ↦ [unit, prim]) [byTest] dHyp) [] [] φ
      | dbgTrace "nodePrimitive: not proved" fun _ ↦ none
    pure (⟨0, [], [], φ⟩, d))

/-- A constructor's definition without a variable field is sound at states
({name}`soundAtT`) of which the invariant's parts hold, where the typing reads the datatype's
atom as the datatype and the marker's constructors have the constructor's: the soundness at
every context and environment ({lit}`ctorPlain`) at the empty ones ({name}`soundOfFormAll`).
Of {lit}`ctorPlain`'s hypotheses, the atoms' properties are the invariant's
({name}`fieldAllOf`, {name}`numOfKws`), the constructors' atoms are excluded from the
abbreviated names and the node's name from the names and the environment's, the fields' types
cohere with the markers' reading where the typing reads them, as it does where the definition
has a type ({name}`fieldsTypedRead`, {name}`cohFields`), and the fields' annotations read as
types where the reader resolves the definition ({name}`fieldsResolvedRead`). In the context of
the fields' types, the datatype's atom's characters, the constructor's position, the
representation of no variable field, the declarations, the kernel's types of the globals, the
numeral abbreviations, the names, the type abbreviations, the typing environment and the
relation's context. -/
def ctorSoundAt (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("ctorSoundAt", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let nil := nilT treeTy
    let some (Internal.Entry.language c) := E[ix "ctorPlain"]?
      | dbgTrace "ctorSoundAt: the constructors' soundness is absent" fun _ ↦ none
    let Γ₀ := [Ls, Ls, treeTy, treeTy, Ls, Ls, Ls, Ls, Ls, T.envTy, Defs3.ctxTy]
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (fsA, csA, jA, rtyA, dvA, GA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5)
    let (numsA, namesA, tysA, EA, RA) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10)
    let z := pc P "Datatype.sx2" [pc P "Datatype.aNil" [], pc P "Datatype.aT" []]
    let nrA (Γ : List Tree) : Term := pc P "Datatype/Txs.length" [fsA Γ]
    let bodyA (Γ : List Tree) : Term := ctorBody P (csA Γ) (jA Γ) (nrA Γ) z (fsA Γ)
    let XA (Γ : List Tree) : Term := nestT P (binderFold P (nrA Γ) (fsA Γ)) (bodyA Γ)
    -- the terms of the context of the constructors' soundness
    let σ (Γ : List Tree) : List Term := [fsA Γ, dvA Γ, nrA Γ, z, rtyA Γ, leafT bnilT, jA Γ,
      csA Γ, EA Γ, nil, nil, tysA Γ, namesA Γ, numsA Γ, RA Γ]
    let hC (i : ℕ) : Term := Internal.instTerm [] (σ Γ₀) (c.hyps.getD i Term.star)
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let synA (Γ : List Tree) : Term := pc P "Typing.synIn" [EA Γ, nil, XA Γ]
    let resA (Γ : List Tree) : Term := pc P "Reader.resolve" [tysA Γ, namesA Γ,
      pc P "Reader.expandNums" [numsA Γ, pc P "Datatype.eraseExpr" [XA Γ]], nil]
    let ms := Term.snd (RA Γ₀)
    let hyps := [T.numsT (EA Γ₀) (numsA Γ₀), T.kwsT (numsA Γ₀),
      T.globT (RA Γ₀) (EA Γ₀) (namesA Γ₀), T.namesT (namesA Γ₀),
      S.allL (userPred P) (namesA Γ₀), noSortsT P (EA Γ₀), aliasT P (dvA Γ₀) (EA Γ₀) ms,
      aliasKwT P (dvA Γ₀), staticT P ms, digitsFixedT P, hC 10, hC 11]
    let (hNums, hKws, hGlob, hNames, hUser, hSorts) := (0, 1, 2, 3, 4, 5)
    let (hAlias, hAliasKw, hStatic, hDigits, hRead, hLast) := (6, 7, 8, 9, 10, 11)
    let a : Internal.Thm := ⟨0, Γ₀, hyps,
      [truth o (isSome (synA Γ₀)), truth o (isSome (resA Γ₀)),
        truth o (isSome (pc P "Check.typeIn" [GA Γ₀, nil, get (resA Γ₀)]))].foldr
        (Internal.Logic.imp o)
        (S.conv (Term.lam nat (S.evN (Term.fst (sh 1 (RA Γ₀))) (v 0) (sh 1 nil)
            (sh 1 (get (resA Γ₀)))))
          (T.relT (RA Γ₀) (get (synA Γ₀))))⟩
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let at' (m : String) (k : Deducer) : Deducer := stage s!"ctorSoundAt: {m}" k
    let hypOr := hypOrK K
    let lastHyp : Deducer := last hypOr
    let nodeN := atomNameT (pc P "Recognize.rNode" [])
    let aNodeN := atomNameT (pc P "Datatype.aNode" [])
    -- a test decided false does not hold
    let decidedNot : Deducer := dImpI L (lastFalse K)
    -- the node's name is no numeral name of the environment's: one is abbreviated, and the
    -- node's name is excluded from the abbreviated names
    let noNum : Deducer := dImpI L <| last fun iHas ↦
      dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) hNums <|
      K.allEΓ (fun _ ↦ aNodeN) <| K.conjE <| fun Γ Φ ψ ↦
      dImpE L (Φ.length - 2) (at' "a numeral name" (K.byHyp iHas)) (K.exE <| K.conjE <|
        fun Γ₁ Φ₁ ψ₁ ↦ normHyps K [Φ₁.length - 2] (
          dRwHyp (evalRw K.G K.E [.delta (T.q + 5 + 2 * nFolds)] .head) hKws <|
          K.allEΓ (fun _ ↦ aNodeN) <| K.impE (at' "the node abbreviated" (K.solve 3)) <|
          K.impE (at' "the node excluded"
            (K.cutThm "ctorExcluded1" (fun _ ↦ []) lastHyp)) <| lastFalse K) Γ₁ Φ₁ ψ₁) Γ Φ ψ
    -- the end of the list of a constructor without a variable field
    let baseD : Deducer := dAllI L <| dAllI L <| fun Γ₃ Φ₃ ψ₃ ↦
      let cxA (Γ : List Tree) : Term := v (1 + (Γ.length - Γ₃.length))
      let envA (Γ : List Tree) : Term := v (Γ.length - Γ₃.length)
      (dImpI L <| dImpI L <| dImpI L <|
        applyThm K "baseNil" (fun Γ ↦ [rtyA Γ, cxA Γ, envA Γ, scopeOf P (numsA Γ) (cxA Γ),
            tysA Γ, namesA Γ, numsA Γ, RA Γ]) [decidedNot, decidedNot] lastHyp) Γ₃ Φ₃ ψ₃
    let main : Deducer := dImpI L <| dImpI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
      let (iSyn, iRes, iKer) := (Φ₁.length - 3, Φ₁.length - 2, Φ₁.length - 1)
      (dConjE L hStatic <| K.conjE <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (iMarkers, iDec) := (Φ₂.length - 6, Φ₂.length - 2)
        (applyThm K "numOfKws" (fun Γ ↦ [numsA Γ])
          [hypOr hKws, hypOr iDec, hypOr hDigits] <| last fun iNumT ↦
        applyThm K "fieldAllOf" (fun Γ ↦ [namesA Γ, numsA Γ, EA Γ, RA Γ])
          [hypOr hKws, hypOr iNumT, hypOr hGlob, hypOr hUser] <| last fun iField ↦
        cutBy (fun Γ ↦ notTest o (pc P "Typing.hasName" [aNodeN, pc P "Typing.envNums" [EA Γ]]))
          (at' "the node no numeral name" noNum) <| last fun iNoNum ↦
        plainAtoms K T (ctorAtoms P) numsA hKws (lemmas := ctorExcludedNames P) <|
        decideIn K (fun Γ ↦ isSome (pc P "Reader.indexOf" [nodeN, namesA Γ]))
          (applyThm K "globAbsent" (fun Γ ↦ [aNodeN, namesA Γ, EA Γ, RA Γ])
            [hypOr hGlob, at' "the node no name" decidedNot] <| last fun iNoDef ↦
          K.cutThm "fieldsTypedRead" (fun Γ ↦ [fsA Γ]) <| K.allEΓ bodyA <| K.allEΓ nrA <|
          K.allEΓ EA <| K.allEΓ (fun _ ↦ nil) <|
          K.impE (at' "the definition typed" (K.byHyp iSyn)) <| K.conjE <|
          last fun iTypedIn ↦
          let iReadTys := iTypedIn - 1
          K.cutThm "cohFields" (fun Γ ↦ [fsA Γ]) <| K.allEΓ RA <| K.allEΓ dvA <| K.allEΓ EA <|
          last fun hI ↦ impEs L hI [at' "the aliases" (hypOr hAlias),
            at' "the aliases' keywords" (hypOr hAliasKw), at' "the markers' names" (hypOr iMarkers),
            at' "no sorts" (hypOr hSorts), at' "the fields' types read" (K.byHyp iReadTys)] <|
          last fun iCoh ↦
          K.cutThm "fieldsResolvedRead" (fun Γ ↦ [fsA Γ]) <| K.allEΓ bodyA <| K.allEΓ nrA <|
          K.allEΓ EA <| K.allEΓ numsA <| K.allEΓ tysA <| K.allEΓ namesA <|
          K.allEΓ (fun _ ↦ nil) <| last fun hI ↦ impEs L hI [at' "the fields' atoms" (hypOr iField),
            at' "the abstraction's keyword" decidedNot,
            at' "the definition resolved" (K.byHyp iRes)] <| K.conjE <|
          last fun iResIn ↦
          let iReadOk := iResIn - 1
          applyThm K "ctorPlain" σ [at' "the numerals" (hypOr hNums),
            at' "the atoms" (hypOr iField), at' "the list's construction" decidedNot,
            at' "the fields cohere" (hypOr iCoh), at' "the list's end" baseD,
            at' "the node no definition" (hypOr iNoDef),
            at' "the node no numeral" (hypOr iNoNum), at' "the numerals read" (hypOr iNumT),
            at' "the node no name" decidedNot, at' "the node plain" decidedNot,
            at' "the datatype read" (hypOr hRead), at' "the marker's constructor" (hypOr hLast),
            at' "the abstraction plain" decidedNot, at' "the annotations read" (hypOr iReadOk),
            at' "the empty list plain" decidedNot, at' "the trees' type plain" decidedNot] <|
          applyThm K "soundOfFormAll" (fun Γ ↦ [XA Γ, GA Γ, numsA Γ, namesA Γ, tysA Γ, EA Γ,
            RA Γ]) [at' "sound at every context" lastHyp] <| last fun hI ↦ impEs L hI
            [K.byHyp iSyn, K.byHyp iRes, K.byHyp iKer] <| at' "the value" lastHyp)
          (at' "the node a name" <|
            dRwHyp (evalRw K.G K.E [.delta (T.q + 4 + 2 * nFolds)] .head) hNames <|
            K.allEΓ (fun _ ↦ nodeN) <| K.impE (K.solve 3) <|
            K.impE (K.cutThm "nodePrimitive" (fun _ ↦ []) lastHyp) <| lastFalse K))
          Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    let some d := main a.ctx a.hyps a.concl
      | dbgTrace "ctorSoundAt: not proved" fun _ ↦ none
    pure (a, d))

/-- A goal by normalization, the first difference of an equation's sides traced where they
differ. -/
def byNormTraced (K : Kit) (name : String) : Deducer := fun Γ Φ ψ ↦
  (K.byNorm Γ Φ ψ).orElse fun _ ↦
    let nf (t : Term) : Option Term := (evalRw K.G K.E (K.rules Φ) .full Γ Φ t).map Prod.fst
    let d := (Internal.eqParts ψ).bind fun (l, r) ↦
      (nf l).bind fun x ↦ (nf r).bind fun y ↦ firstDiff x y
    dbgTrace s!"{name}: {d.map fun (x, y) ↦
      s!"{showT x}\n  vs {showT y}"}" fun _ ↦ none

/-- The abstractions over the binders of a concatenation around a form are those over the first
list's around those over the second's: by induction on the first. In the context of the first
list, under the second and the form. -/
def nestAppend (P : Prog) (S : Defs) : Step :=
  ("nestAppend", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifiers: the form v0, the second list v1, the first v2
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o treeTy (Term.lam treeTy
      (Term.eq (nestT P (pc P "Prelude.append" [v 2, v 1]) (v 0))
        (nestT P (v 2) (nestT P (v 1) (v 0)))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let base : Deducer := dAllI L <| dAllI L <| byNormTraced K "nestAppend: none"
    -- a construction: the head v(0), the tail v(1), the second list v(2), the form v(3)
    let step : Deducer := dAllI L <| dAllI L <| fun Γ Φ ψ ↦
      dAllE L K.G K.E 0 (at_ 2 Γ) (K.allEΓ (at_ 3) <| normLastK K <|
        byNormTraced K "nestAppend: a binder") Γ Φ ψ
    listInduction "nestAppend" φ base step)

/-- The fields' types of a constructor with a variable field: its elements after its atom
without the last two, the variable fields' keyword and the variable field's type. -/
def varFieldsT (P : Prog) (rest : Term) : Term :=
  pc P "Datatype.dropLast" [pc P "Datatype.dropLast" [rest]]

/-- The type of a constructor's variable field: the last of its elements after its atom. -/
def varTypeT (P : Prog) (rest : Term) : Term :=
  let subT := (primT Kernel.Prim.sub).getD Term.star
  pc P "Datatype.nthTx" [rest,
    apps subT [pc P "Datatype/Txs.length" [rest], leafT (numeral 1)]]

/-- The body of the definition of a constructor with a variable field, of the characters of the
datatype's atom, the constructor's position and its elements after its atom: the abstractions
over the fields' binders and the variable field's, of the lists of its type, around the
coercion to the datatype of the node of the position over the fields' values and the variable
field's. -/
def ctorVarDefT (P : Prog) (csd j rest : Term) : Term :=
  let fs := varFieldsT P rest
  let nf := pc P "Datatype/Txs.length" [fs]
  let aRest := pc P "Datatype.aRest" []
  let F := pc P "Datatype.sList" [varTypeT P rest]
  nestT P (pc P "Prelude.append" [binderFold P nf fs,
      consT treeTy (listNode [aRest, F]) (nilT treeTy)])
    (ctorBody P csd j nf (pc P "Typing.tOf" [F, aRest]) fs)

/-- The typing's form of a list of two forms is the list of their forms, its sides in the
normal form of the rules of a kit without the datatype language's vocabulary, the typing's
step at the list unfolded in the proof. In the context of the second form, the first and the
typing environment. -/
def rawPairEq (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("rawPairEq", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Γ := [treeTy, treeTy, T.envTy]
    let l ← nfE K.G K.E (K.rules []) Γ (rawT T (v 2) (listNode [v 1, v 0]))
    let r ← nfE K.G K.E (K.rules []) Γ (listNode [rawT T (v 2) (v 1), rawT T (v 2) (v 0)])
    -- the fold at the list by the vocabulary's rules, its step unfolded
    let Kv : Kit := ⟨P, S, E, ix, vocab3.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let some d := byMode .full K.G K.E 0 (Kv.rules [] ++ [.delta (T.argIdx 1)]) Γ [] l r
      | dbgTrace s!"rawPairEq: {showT l}\n  vs {showT r}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The typing reads a type of lists where it reads the elements' type, as the type of lists of
it: where it reads the form of the lists of a form, it reads the form, and the first child of
the type read is the type of the form. In the context of the form and the typing
environment. -/
def readTyList (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("readTyList", fun ix E ↦ do
    let K : Kit := ⟨aliasProg P, S, E, ix,
      lookupEqNames ++ ["hasNameNil", "rawAtomEq", "rawPairEq", "rtFst", "rtKids"]⟩
    let L := K.L
    let o := P.o
    let childT ← primT Kernel.Prim.child
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let read (Ev F : Term) : Term := pc P "Typing.readTy" [Ev, rawT T Ev F]
    let listOf (F : Term) : Term := pc P "Datatype.sList" [F]
    let (F, Ev) := (v 0, v 1)
    let a : Internal.Thm := ⟨0, [treeTy, T.envTy], [truth o (isSome (read Ev (listOf F)))],
      Internal.Logic.conj o (truth o (isSome (read Ev F)))
        (Term.eq (apps childT [get (read Ev (listOf F)), leafT bnilT]) (get (read Ev F)))⟩
    let some d := (decideOpt K (fun Γ ↦ read (atPos 0 Γ) (atPos 1 Γ))
        (stage "readTyList: no type" (K.hypFalse 0))
        (dConjI L (stage "readTyList: read" (K.solve 3))
          (stage "readTyList: the elements' type" (byNormTraced K "readTyList"))))
        a.ctx a.hyps a.concl
      | dbgTrace "readTyList: not proved" fun _ ↦ none
    pure (a, d))

/-- The reader's resolution of an abstraction over one binder, an atom named by no abbreviation
and no keyword of the erasure whose characters the expansion of the numeral abbreviations
fixes, reads the binder's annotation as a type ({name}`readOkT`): the abstraction's erasure
({lit}`eraseLam`) resolves, so its binders read ({name}`lamBindersRead`) and the annotation
reads ({name}`binderTypeRead`), as the option of a type ({name}`readTypeSome`). In the context
of the body, the annotation, the atom's characters, the scope, the type abbreviations, the
definitions' names and the numeral abbreviations. -/
def restBinderRead (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("restBinderRead", fun ix E ↦ do
    let K := lamKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let Γ₀ := [treeTy, treeTy, Ls, Ls, Ls, Ls, Ls]
    let rLam := pc P "Recognize.rLam" []
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let er (t : Term) : Term := pc P "Datatype.eraseExpr" [t]
    let atom (cs : Term) : Term := nodeT (Term.pair (numeral 1) cs)
    let abbr (a nums : Term) : Term := isSome (pc P "Reader.lookupAbbrev" [atomNameT a, nums])
    let (b, F, cs, scope, tys, names, nums) := (v 0, v 1, v 2, v 3, v 4, v 5, v 6)
    let fn := Term.lam treeTy (pc P "Reader.expandNums" [sh 1 nums, v 0])
    let a : Internal.Thm := ⟨0, Γ₀,
      [notTest o (abbr rLam nums), notTest o (abbr (atom cs) nums),
        truth o (pc P "charsFixed" [fn, cs])] ++
      binderKws.map (fun kw ↦ notTest o (pc P "Typing.namedTx" [atom cs, pc P kw []])) ++
      [truth o (isSome (pc P "Reader.resolve" [tys, names,
        pc P "Reader.expandNums" [nums, er (lamForm P (atom cs) F b)], scope]))],
      readOkT P nums tys F⟩
    let hRes := 3 + binderKws.length
    let (numsA, namesA, tysA, scopeA, csA, FA, bA) :=
      (atPos 0, atPos 1, atPos 2, atPos 3, atPos 4, atPos 5, atPos 6)
    let readA (Γ : List Tree) : Term := pc P "Reader.readType" [tysA Γ,
      pc P "Reader.expandNums" [numsA Γ, er (FA Γ)]]
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let at' (m : String) (k : Deducer) : Deducer := stage s!"restBinderRead: {m}" k
    -- a hypothesis and the goal, rewritten by equations alone
    let bits := [D.bnil, D.b0, D.b1].map Internal.NormRule.delta
    let raw₁ : List Internal.NormRule := Translation.baseRules ++ bits
    let rawHyp (rs : List Internal.NormRule) (h : ℕ) : Deducer :=
      dRwHyp (evalRw K.G K.E rs .full) h <| dRwBy (evalRw K.G K.E rs .full) dHyp
    let some d := (
        applyThm K "eraseLam" (fun Γ ↦ [bA Γ, FA Γ, csA Γ])
          ((List.range binderKws.length).map fun i ↦ hypOrK K (3 + i)) <|
        last fun hEr₀ ↦ dRwHyp (evalRw K.G K.E raw₁ .full) hEr₀ <| last fun hEr ↦
        applyThm K "lamBindersRead" (fun Γ ↦ [listNode [listNode [atom (csA Γ), er (FA Γ)]],
            er (bA Γ), scopeA Γ, tysA Γ, namesA Γ, numsA Γ])
          [at' "the keyword" (hypOrK K 0),
            at' "the abstraction resolved" (rawHyp (raw₁ ++ [.hyp hEr]) hRes)] <|
        last fun hBs ↦
        applyThm K "binderTypeRead" (fun Γ ↦ [csA Γ, er (FA Γ), numsA Γ, tysA Γ])
          [at' "not abbreviated" (hypOrK K 1), at' "fixed" (hypOrK K 2),
            at' "the binders read" (hypOrK K hBs)] <| last fun hRead ↦
        applyThm K "readTypeSome" (fun Γ ↦ [pc P "Reader.expandNums" [numsA Γ, er (FA Γ)],
            tysA Γ]) [at' "a type read" (hypOrK K hRead)] <| last fun hEq ↦
        at' "the type" fun Γ Φ ψ ↦
          dExI L K.G K.E (pc P "Prelude.get" [readA Γ]) (eqByHyp K hEq) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "restBinderRead: not proved" fun _ ↦ none
    let _ := (b, F, scope, tys, names)
    pure (a, d))

/-- A constructor's definition with a variable field is sound at states
({name}`soundAtT`) of which the invariant's parts hold, where the typing reads the datatype's
atom as the datatype and the marker's constructors have the constructor's: the soundness at
every context and environment ({lit}`ctorVar`) at the empty ones ({name}`soundOfFormAll`). Of
{lit}`ctorVar`'s hypotheses beyond those of a constructor without one ({name}`ctorSoundAt`):
the abstractions are those over the fields' binders around that over the variable field's
({name}`nestAppend`), whose annotation, the lists of the field's type, the typing reads where
the definition has a type and the reader where it resolves ({name}`restBinderRead`); the type
read is the lists of the field's type's ({name}`readTyList`), with which the field's type
coheres ({name}`cohOfRead`); and the variable field's atom, the implementation's, is excluded
from the abbreviated names, and names no definition and no primitive. In the context of the
constructor's elements after its atom, the characters of the datatype's atom, the
constructor's position, the declarations, the kernel's types of the globals, the numeral
abbreviations, the names, the type abbreviations, the typing environment and the relation's
context. -/
def ctorSoundVarAt (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("ctorSoundVarAt", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let nil := nilT treeTy
    let some (Internal.Entry.language c) := E[ix "ctorVar"]?
      | dbgTrace "ctorSoundVarAt: the constructors' soundness is absent" fun _ ↦ none
    let Γ₀ := [Ls, Ls, treeTy, Ls, Ls, Ls, Ls, Ls, T.envTy, Defs3.ctxTy]
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (restA, csA, jA, dvA, GA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4)
    let (numsA, namesA, tysA, EA, RA) := (at_ 5, at_ 6, at_ 7, at_ 8, at_ 9)
    let aRest := pc P "Datatype.aRest" []
    let restN := atomNameT aRest
    let fsA (Γ : List Tree) : Term := varFieldsT P (restA Γ)
    let vtA (Γ : List Tree) : Term := varTypeT P (restA Γ)
    let FA (Γ : List Tree) : Term := pc P "Datatype.sList" [vtA Γ]
    let nfA (Γ : List Tree) : Term := pc P "Datatype/Txs.length" [fsA Γ]
    let rtyA (Γ : List Tree) : Term := pc P "Datatype.expandAliases" [dvA Γ, vtA Γ]
    let zA (Γ : List Tree) : Term := pc P "Typing.tOf" [FA Γ, aRest]
    let bodyA (Γ : List Tree) : Term := ctorBody P (csA Γ) (jA Γ) (nfA Γ) (zA Γ) (fsA Γ)
    let binderA (Γ : List Tree) : Term := listNode [aRest, FA Γ]
    -- the abstraction over the variable field's binder around the body
    let csR := call D.children [] [aRest]
    let atomR := nodeT (Term.pair (numeral 1) csR)
    let lamA (Γ : List Tree) : Term := lamForm P atomR (FA Γ) (bodyA Γ)
    let XA (Γ : List Tree) : Term := ctorVarDefT P (csA Γ) (jA Γ) (restA Γ)
    -- the terms of the context of the constructors' soundness
    let σ (Γ : List Tree) : List Term := [fsA Γ, dvA Γ, nfA Γ, zA Γ, rtyA Γ, FA Γ, jA Γ,
      csA Γ, EA Γ, nil, nil, tysA Γ, namesA Γ, numsA Γ, RA Γ]
    let hC (i : ℕ) : Term := Internal.instTerm [] (σ Γ₀) (c.hyps.getD i Term.star)
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let synA (Γ : List Tree) : Term := pc P "Typing.synIn" [EA Γ, nil, XA Γ]
    let resA (Γ : List Tree) : Term := pc P "Reader.resolve" [tysA Γ, namesA Γ,
      pc P "Reader.expandNums" [numsA Γ, pc P "Datatype.eraseExpr" [XA Γ]], nil]
    let ms := Term.snd (RA Γ₀)
    let hyps := [T.numsT (EA Γ₀) (numsA Γ₀), T.kwsT (numsA Γ₀),
      T.globT (RA Γ₀) (EA Γ₀) (namesA Γ₀), T.namesT (namesA Γ₀),
      S.allL (userPred P) (namesA Γ₀), noSortsT P (EA Γ₀), aliasT P (dvA Γ₀) (EA Γ₀) ms,
      aliasKwT P (dvA Γ₀), staticT P ms, digitsFixedT P, hC 10, hC 11]
    let (hNums, hKws, hGlob, hNames, hUser, hSorts) := (0, 1, 2, 3, 4, 5)
    let (hAlias, hAliasKw, hStatic, hDigits, hRead, hLast) := (6, 7, 8, 9, 10, 11)
    let a : Internal.Thm := ⟨0, Γ₀, hyps,
      [truth o (isSome (synA Γ₀)), truth o (isSome (resA Γ₀)),
        truth o (isSome (pc P "Check.typeIn" [GA Γ₀, nil, get (resA Γ₀)]))].foldr
        (Internal.Logic.imp o)
        (S.conv (Term.lam nat (S.evN (Term.fst (sh 1 (RA Γ₀))) (v 0) (sh 1 nil)
            (sh 1 (get (resA Γ₀)))))
          (T.relT (RA Γ₀) (get (synA Γ₀))))⟩
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let at' (m : String) (k : Deducer) : Deducer := stage s!"ctorSoundVarAt: {m}" k
    let hypOr := hypOrK K
    let lastHyp : Deducer := last hypOr
    let nodeN := atomNameT (pc P "Recognize.rNode" [])
    let aNodeN := atomNameT (pc P "Datatype.aNode" [])
    let prims := pc P "Reader.primNames" []
    -- a test decided false does not hold
    let decidedNot : Deducer := dImpI L (lastFalse K)
    -- the node's name is no numeral name of the environment's: one is abbreviated, and the
    -- node's name is excluded from the abbreviated names
    let noNum : Deducer := dImpI L <| last fun iHas ↦
      dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) hNums <|
      K.allEΓ (fun _ ↦ aNodeN) <| K.conjE <| fun Γ Φ ψ ↦
      dImpE L (Φ.length - 2) (at' "a numeral name" (K.byHyp iHas)) (K.exE <| K.conjE <|
        fun Γ₁ Φ₁ ψ₁ ↦ normHyps K [Φ₁.length - 2] (
          dRwHyp (evalRw K.G K.E [.delta (T.q + 5 + 2 * nFolds)] .head) hKws <|
          K.allEΓ (fun _ ↦ aNodeN) <| K.impE (at' "the node abbreviated" (K.solve 3)) <|
          K.impE (at' "the node excluded"
            (K.cutThm "ctorExcluded1" (fun _ ↦ []) lastHyp)) <| lastFalse K) Γ₁ Φ₁ ψ₁) Γ Φ ψ
    -- no name of a closed list is the implementation's: each conjunct's test refuted
    let noImpl : Deducer := Nat.rec (motive := fun _ ↦ Deducer) (K.solve 1) (fun _ rec Γ Φ ψ ↦
      (K.solve 1 Γ Φ ψ).orElse fun _ ↦
        K.norm (dConjI L (dImpI L (lastFalse K)) rec) Γ Φ ψ) 96
    -- the variable field's atom's name, the implementation's, without an index among names
    -- none of which is
    let absent (xs : List Tree → Term) (none : Deducer) (k : Deducer) : Deducer :=
      K.cutThm "implAbsent" (fun Γ ↦ [xs Γ]) <| K.allEΓ (fun _ ↦ restN) <| K.impE none <|
      K.impE (at' "the variable field's name the implementation's" (K.solve 3)) k
    let restNoDef : Deducer := absent namesA (hypOr hUser) <| last fun iIdx ↦
      applyThm K "globAbsent" (fun Γ ↦ [restN, namesA Γ, EA Γ, RA Γ])
        [hypOr hGlob, K.byHyp iIdx] (last K.byHyp)
    let restNoPrim : Deducer := absent (fun _ ↦ prims) (at' "the primitives' names" noImpl) <|
      last K.byHyp
    let main : Deducer := dImpI L <| dImpI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
      let (iSyn, iRes, iKer) := (Φ₁.length - 3, Φ₁.length - 2, Φ₁.length - 1)
      (dConjE L hStatic <| K.conjE <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (iMarkers, iDec) := (Φ₂.length - 6, Φ₂.length - 2)
        (applyThm K "numOfKws" (fun Γ ↦ [numsA Γ])
          [hypOr hKws, hypOr iDec, hypOr hDigits] <| last fun iNumT ↦
        applyThm K "fieldAllOf" (fun Γ ↦ [namesA Γ, numsA Γ, EA Γ, RA Γ])
          [hypOr hKws, hypOr iNumT, hypOr hGlob, hypOr hUser] <| last fun iField ↦
        cutBy (fun Γ ↦ notTest o (pc P "Typing.hasName" [aNodeN, pc P "Typing.envNums" [EA Γ]]))
          (at' "the node no numeral name" noNum) <| last fun iNoNum ↦
        -- the abstractions: those over the fields' binders around that over the variable
        -- field's
        K.cutThm "nestAppend" (fun Γ ↦ [binderFold P (nfA Γ) (fsA Γ)]) <|
        K.allEΓ (fun Γ ↦ consT treeTy (binderA Γ) nil) <| K.allEΓ bodyA <| normLastK K <|
        plainAtoms K T (ctorAtoms P ++ [restN]) numsA hKws
          (lemmas := ctorExcludedNames P ++ [(restN, "restExcluded")]) <|
        decideIn K (fun Γ ↦ isSome (pc P "Reader.indexOf" [nodeN, namesA Γ]))
          (applyThm K "globAbsent" (fun Γ ↦ [aNodeN, namesA Γ, EA Γ, RA Γ])
            [hypOr hGlob, at' "the node no name" decidedNot] <| last fun iNoDef ↦
          -- the typing: the fields' types and the variable field's annotation read
          K.cutThm "fieldsTypedRead" (fun Γ ↦ [fsA Γ]) <| K.allEΓ lamA <| K.allEΓ nfA <|
          K.allEΓ EA <| K.allEΓ (fun _ ↦ nil) <|
          K.impE (at' "the definition typed" (K.byHyp iSyn)) <| K.conjE <|
          last fun iTypedIn ↦
          let iReadTys := iTypedIn - 1
          K.exE <| fun Γ₃ Φ₃ ψ₃ ↦
          let cxA (Γ : List Tree) : Term := v (Γ.length - Γ₃.length)
          (applyThm K "lamTypedOne" (fun Γ ↦ [bodyA Γ, FA Γ, atomR, cxA Γ, EA Γ])
            [at' "the variable field's abstraction typed" (last K.byHyp)] <|
          K.conjE <| K.conjE <| fun Γ₄ Φ₄ ψ₄ ↦
          let iReadF := Φ₄.length - 4
          (applyThm K "readTyList" (fun Γ ↦ [vtA Γ, EA Γ])
            [at' "the lists' type read" (K.byHyp iReadF)] <| K.conjE <| normLastK K <|
          fun Γ₅ Φ₅ ψ₅ ↦
          let iReadVt := Φ₅.length - 3
          (K.cutThm "cohFields" (fun Γ ↦ [fsA Γ]) <| K.allEΓ RA <| K.allEΓ dvA <|
            K.allEΓ EA <| last fun hI ↦ impEs L hI [at' "the aliases" (hypOr hAlias),
              at' "the aliases' keywords" (hypOr hAliasKw),
              at' "the markers' names" (hypOr iMarkers), at' "no sorts" (hypOr hSorts),
              at' "the fields' types read" (K.byHyp iReadTys)] <| last fun iCoh ↦
          applyThm K "cohOfRead" (fun Γ ↦ [vtA Γ, EA Γ, dvA Γ, RA Γ])
            [at' "the aliases" (hypOr hAlias), at' "the aliases' keywords" (hypOr hAliasKw),
              at' "the markers' names" (hypOr iMarkers), at' "no sorts" (hypOr hSorts),
              at' "the variable field's type read" (K.byHyp iReadVt)] <| last fun iCohVt ↦
          -- the reader: the fields' annotations and the variable field's read
          K.cutThm "fieldsResolvedRead" (fun Γ ↦ [fsA Γ]) <| K.allEΓ lamA <| K.allEΓ nfA <|
          K.allEΓ EA <| K.allEΓ numsA <| K.allEΓ tysA <| K.allEΓ namesA <|
          K.allEΓ (fun _ ↦ nil) <| last fun hI ↦ impEs L hI
            [at' "the fields' atoms" (hypOr iField),
              at' "the abstraction's keyword" decidedNot,
              at' "the definition resolved" (K.byHyp iRes)] <| K.conjE <|
          last fun iResIn ↦
          let iReadOk := iResIn - 1
          K.exE <| fun Γ₆ Φ₆ ψ₆ ↦
          let scopeA (Γ : List Tree) : Term := v (Γ.length - Γ₆.length)
          (applyThm K "restBinderRead" (fun Γ ↦ [bodyA Γ, FA Γ, csR, scopeA Γ, tysA Γ,
              namesA Γ, numsA Γ])
            ([at' "the abstraction's keyword" decidedNot,
              at' "the variable field's atom plain" decidedNot,
              at' "the variable field's atom fixed" (fun Γ Φ ψ ↦
                let Kl := lamKit P S T ix E
                dRwBy (evalRw Kl.G Kl.E (Kl.rules Φ ++ [.delta (P.idx "charsFixed"),
                  .delta (T.argIdx 3)]) .full) (Kl.solve 3) Γ Φ ψ)] ++
              binderKws.map (fun kw ↦ at' s!"the variable field's atom not {kw}" decidedNot) ++
              [at' "the variable field's abstraction resolved" lastHyp]) <|
          last fun iReadOkF ↦
          -- the variable field's type coheres with the marker's reading of it
          let coheres : Deducer := at' "the variable field coheres" (K.byHyp iCohVt)
          -- the end of the list of a constructor with a variable field
          let baseD : Deducer := dAllI L <| dAllI L <| fun Γ₇ Φ₇ ψ₇ ↦
            let cx (Γ : List Tree) : Term := v (1 + (Γ.length - Γ₇.length))
            let env (Γ : List Tree) : Term := v (Γ.length - Γ₇.length)
            (dImpI L <| last fun hEnv ↦
              applyThm K "baseVar" (fun Γ ↦ [FA Γ, rtyA Γ, cx Γ, EA Γ, env Γ,
                  scopeOf P (numsA Γ) (cx Γ), tysA Γ, namesA Γ, numsA Γ, RA Γ])
                [hypOr hNums, K.byHyp hEnv, decidedNot, restNoDef, restNoPrim, decidedNot,
                  coheres] lastHyp) Γ₇ Φ₇ ψ₇
          applyThm K "ctorVar" σ [at' "the numerals" (hypOr hNums),
            at' "the atoms" (hypOr iField), at' "the list's construction" decidedNot,
            at' "the fields cohere" (hypOr iCoh), at' "the list's end" baseD,
            at' "the node no definition" (hypOr iNoDef),
            at' "the node no numeral" (hypOr iNoNum), at' "the numerals read" (hypOr iNumT),
            at' "the node no name" decidedNot, at' "the node plain" decidedNot,
            at' "the datatype read" (hypOr hRead), at' "the marker's constructor" (hypOr hLast),
            at' "the abstraction plain" decidedNot, at' "the annotations read" (hypOr iReadOk),
            at' "the variable field's atom plain" decidedNot,
            at' "the variable field's atom no definition" restNoDef,
            at' "the variable field's atom no primitive" restNoPrim,
            at' "the variable field's atom not the unit value" decidedNot, coheres,
            at' "the variable field's annotation read" (hypOr iReadOkF)] <|
          applyThm K "soundOfFormAll" (fun Γ ↦ [XA Γ, GA Γ, numsA Γ, namesA Γ, tysA Γ, EA Γ,
            RA Γ]) [at' "sound at every context" lastHyp] <| last fun hI ↦ impEs L hI
            [K.byHyp iSyn, K.byHyp iRes, K.byHyp iKer] <| at' "the value" lastHyp)
            Γ₆ Φ₆ ψ₆) Γ₅ Φ₅ ψ₅) Γ₄ Φ₄ ψ₄) Γ₃ Φ₃ ψ₃)
          (at' "the node a name" <|
            dRwHyp (evalRw K.G K.E [.delta (T.q + 4 + 2 * nFolds)] .head) hNames <|
            K.allEΓ (fun _ ↦ nodeN) <| K.impE (K.solve 3) <|
            K.impE (K.cutThm "nodePrimitive" (fun _ ↦ []) lastHyp) <| lastFalse K))
          Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    let some d := main a.ctx a.hyps a.concl
      | dbgTrace "ctorSoundVarAt: not proved" fun _ ↦ none
    pure (a, d))

end GebTests.Prototypes.FreeTopos.Datatypes

end
