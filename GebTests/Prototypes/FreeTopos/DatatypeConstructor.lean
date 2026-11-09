/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeRecognizer
public meta import GebTests.Prototypes.FreeTopos.DatatypeRecognizer -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The constructors of datatypes

The definition the expansion of the datatype language writes for a constructor is related to its
type: the abstractions over its fields, each of the field's type, around the coercion to the
datatype of the node of the constructor's position over the fields' values. The fields' values are
those the logical relation relates to their types, and the node is a member of the datatype, by the
marker's entry of the constructor.

## Main definitions

* {lit}`constructorCertificates` — the constructors' fields, stored as the certificate
  {lit}`datatype-constructor`.
* {lit}`constructorBodyCertificates` — the constructors' bodies, stored as the certificate
  {lit}`datatype-constructor-body`.
* {lit}`constructorLamCertificates` — the abstractions over their fields, stored as the certificate
  {lit}`datatype-constructor-lam`.
* {lit}`constructorNestCertificates` — the constructors' definitions, stored as the certificate
  {lit}`datatype-constructor-nest`.

## Main statements

* {lit}`ctorPlain` — a constructor without a variable field is sound.
* {lit}`ctorVar` — a constructor with a variable field is sound.

## Implementation notes

The typing of each field's coercion gives the type of the field's value, so that the proof reads
neither the positions of the fields nor the kernel's typing, and the fields' atoms need not be shown
distinct. The soundness is stated at the expression's denotation rather than at a typed kernel term.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, datatypes, constructor, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- The characters of the atom of a constructor's field. -/
def fieldChars (P : Prog) (k : Term) : Term :=
  consT treeTy (leafT (numeral 37)) (consT treeTy (leafT (numeral 102))
    (pc P "Typing.decimalChars" [k]))

/-- The atom of a constructor's field. -/
def fieldAtomT (P : Prog) (k : Term) : Term := nodeT (Term.pair (numeral 1) (fieldChars P k))

/-- The atom of a constructor's field bound in the scope denotes the value the environment holds at
its index, where it names no abbreviation and its number's digits are fixed by the expansion of the
numeral abbreviations. -/
def denFieldVar (P : Prog) : DenRule :=
  let vars := [treeTy, treeTy]
  let at_ := denAt vars
  let (k, w) := (at_ 6, at_ 7)
  let digits := pc P "Typing.decimalChars" [k]
  let form := fieldAtomT P k
  let idx := pc P "Reader.indexOf" [atomNameT form, at_ 4]
  let fn := Term.lam treeTy (pc P "Reader.expandNums" [sh 1 (at_ 1), v 0])
  { name := "denFieldVar", vars, plain := [form],
    more := [truth P.o (pc P "charsFixed" [fn, digits]),
      truth P.o (pc P "Prelude.isSome" [idx]),
      Term.eq (pc P "Prelude.nth" [at_ 5, leafIndex P idx]) (pc P "Prelude.some" [w])],
    form, value := w, levels := 1,
    pre := fun K up k' ↦ K.cutThm "charsFixedEq" (fun Γ ↦ [up digits Γ, atPos 1 Γ])
      (K.impE (K.byHyp 1) (normLastK K (decideIn K (up (pc P "Prelude.isSome" [idx]))
        (K.hypFalse 2) k'))) }

/-- The atom of a constructor's field names no numeral: the first of its characters no digit. -/
def fieldNotNumeral (P : Prog) (S : Defs) : Step :=
  ("fieldNotNumeral", fun ix E ↦ do
    let K := denKit P S ix E
    let thm : Internal.Thm := ⟨0, [treeTy], [],
      Term.eq (pc P "Reader.numeral" [fieldChars P (v 0)]) (pc P "Prelude.none" [])⟩
    let some d := dEq (byMode .full K.G K.E 0 (K.rules [] ++ [.delta (P.idx "Reader.numeral")]))
        thm.ctx thm.hyps thm.concl
      | dbgTrace "fieldNotNumeral: not proved" fun _ ↦ none
    pure (thm, d))

/-- The atom of a variable field bound in the scope denotes the value the environment holds at its
index. -/
def denRestVar (P : Prog) : DenRule :=
  let vars := [treeTy]
  let at_ := denAt vars
  let w := at_ 6
  let form := pc P "Datatype.aRest" []
  let idx := pc P "Reader.indexOf" [atomNameT form, at_ 4]
  { name := "denRestVar", vars, plain := [form],
    more := [truth P.o (pc P "Prelude.isSome" [idx]),
      Term.eq (pc P "Prelude.nth" [at_ 5, leafIndex P idx]) (pc P "Prelude.some" [w])],
    form, value := w, levels := 1,
    pre := fun K up k' ↦ decideIn K (up (pc P "Prelude.isSome" [idx])) (K.hypFalse 1) k' }

/-- The statement that an atom with a type in a named context denotes a value related at the type,
in the scope of the context's names, under the hypotheses and further hypotheses given. In a context
whose variables' positions from 6 are given. -/
def boundThm (P : Prog) (S : Defs) (T : Defs3) (vars : List Tree) (Ev cx form : Term)
    (more : List Term) : Internal.Thm :=
  let o := P.o
  let at_ := denAt vars
  let n := atomNameT form
  let lookup := pc P "Typing.lookupName" [n, cx]
  ⟨0, denCtx vars, [T.numsT Ev (at_ 1), T.envT (at_ 0) cx (at_ 5),
      notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [n, at_ 1]])] ++ more ++
      [notTest o (boundNameT P n), truth o (pc P "Prelude.isSome" [lookup])],
    Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
      (denT P S (sh 1 (at_ 0)) (sh 1 (at_ 3)) (sh 1 (at_ 2)) (sh 1 (at_ 1))
        (sh 1 (scopeOf P (at_ 1) cx)) (sh 1 (at_ 5)) (sh 1 form) (v 0))
      (Term.app (T.relT (sh 1 (at_ 0)) (pc P "Prelude.get" [sh 1 lookup])) (v 0))))⟩

/-- An atom no numeral, with a type in a named context, denotes a value related at the type: its
index by the lookups' agreement ({lit}`lookupAgreeA`, {lit}`lookupAgreeB`), the environment's value
there by the environment's relation to the context, whose entry's name is the atom's. The rule of
the atom's denotation at its value and its further hypotheses are given. -/
def boundRel (T : Defs3) (thm : Internal.Thm) (name rule : String)
    (Ev cx form : List Tree → Term) (notNum : Kit → Deducer) (nMore : ℕ)
    (σ : List Tree → List Term) (K : Kit) : Option Internal.Deriv :=
  let P := K.P
  let L := K.L
  let nAt (Γ : List Tree) : Term := atomNameT (form Γ)
  let scopeAt (Γ : List Tree) : Term := scopeOf P (atPos 1 Γ) (cx Γ)
  let idxAt (Γ : List Tree) : Term := pc P "Reader.indexOf" [nAt Γ, scopeAt Γ]
  let fixedAt (Γ : List Tree) : List Term :=
    [atPos 5 Γ, scopeAt Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
  let (hNB, hLk) := (3 + nMore, 4 + nMore)
  let main : Deducer :=
    K.cutThm "lookupAgreeA" (fun Γ ↦ [cx Γ]) <| K.allEΓ (atPos 1) <| K.allEΓ nAt <|
    K.impE (K.byHyp 2) <| K.impE (K.byHyp hLk) <| fun Γ Φ ψ ↦
    let hI := Φ.length - 1
    K.cutThm "lookupAgreeB" (fun Γ ↦ [cx Γ]) (K.allEΓ (atPos 1) <| K.allEΓ Ev <| K.allEΓ nAt <|
      K.impE (K.byHyp 0) <| K.impE (notNum K) <| K.impE (K.byHyp 2) <| K.impE (K.byHyp hI) <|
      K.conjE <| K.conjE <| normLastK K <| fun Γ Φ ψ ↦
      let hS := Φ.length - 3
      let iAt (Γ : List Tree) : Term := leafIndex P (idxAt Γ)
      dRwHyp (evalRw K.G K.E [.delta (T.q + 1)] .head) 1 (fun Γ Φ ψ ↦
        dAllE L K.G K.E (Φ.length - 1) (iAt Γ) (K.impE (K.byHyp hS) <|
          K.impE (dImpI L fun Γ Φ ψ ↦ dImpE L hNB
            (linkK K s!"{name}: the entry's name" (K.byHyp (Φ.length - 1)))
            (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) <|
          K.exE <| K.conjE fun Γ Φ ψ ↦
            let wAt := atPos (Γ.length - 1)
            let (hE, hR) := (Φ.length - 2, Φ.length - 1)
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ hE) .full) hE
              (applyThm K rule (fun Γ ↦ [wAt Γ] ++ σ Γ ++ fixedAt Γ)
                ([K.byHyp 2] ++ (List.range nMore).map (fun i ↦ K.byHyp (3 + i)) ++
                  [K.byHyp hI, linkK K s!"{name}: the value" K.byNorm])
                (fun Γ Φ ψ ↦ dExI L K.G K.E (wAt Γ) (dConjI L dHyp
                  (linkK K s!"{name}: the relation" (K.byHyp hR))) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
      Γ Φ ψ
  main thm.ctx thm.hyps thm.concl

/-- The context of the atom of a constructor's field in a named context: the number, the context
and the typing environment. -/
def fieldVars (T : Defs3) : List Tree := [treeTy, list treeTy, T.envTy]

/-- The atom of a constructor's field with a type in a named context denotes a value related at the
type, in the scope of the context's names ({name}`boundRel`). -/
def fieldVarRel (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("fieldVarRel", fun ix E ↦ do
    let K := denKit P S ix E
    let P := K.P
    let vars := fieldVars T
    let at_ := denAt vars
    let (Ev, cx, k) := (at_ 6, at_ 7, at_ 8)
    let digits := pc P "Typing.decimalChars" [k]
    let fn := Term.lam treeTy (pc P "Reader.expandNums" [sh 1 (at_ 1), v 0])
    let thm := boundThm P S T vars Ev cx (fieldAtomT P k)
      [truth P.o (pc P "charsFixed" [fn, digits])]
    let (EAt, cxAt, kAt) := (atPos 6, atPos 7, atPos 8)
    let notNum (K : Kit) : Deducer :=
      K.cutThm "fieldNotNumeral" (fun Γ ↦ [kAt Γ]) <| normLastK K <|
        dImpI K.L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let d ← boundRel T thm "fieldVarRel" "denFieldVar" EAt cxAt (fun Γ ↦ fieldAtomT P (kAt Γ))
      notNum 1 (fun Γ ↦ [kAt Γ]) K
    pure (thm, d))

/-- The context of the atom of a variable field in a named context: the context and the typing
environment. -/
def restVars (T : Defs3) : List Tree := [list treeTy, T.envTy]

/-- The atom of a constructor's variable field with a type in a named context denotes a value
related at the type, in the scope of the context's names ({name}`boundRel`). -/
def restVarRel (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("restVarRel", fun ix E ↦ do
    let K := denKit P S ix E
    let P := K.P
    let vars := restVars T
    let at_ := denAt vars
    let (Ev, cx) := (at_ 6, at_ 7)
    let thm := boundThm P S T vars Ev cx (pc P "Datatype.aRest" []) []
    let (EAt, cxAt) := (atPos 6, atPos 7)
    let notNum (K : Kit) : Deducer := dImpI K.L fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E
      (K.rulesEx Φ (Φ.length - 1) ++ [.delta (P.idx "Reader.numeral")]) .full) (Φ.length - 1)
      (dFalse K.L dHyp) Γ Φ ψ
    let d ← boundRel T thm "restVarRel" "denRestVar" EAt cxAt (fun _ ↦ pc P "Datatype.aRest" [])
      notNum 0 (fun _ ↦ []) K
    pure (thm, d))

/-- A deducer given the context and the hypotheses it runs at. -/
def withCtx (f : List Tree → List Term → Deducer) : Deducer := fun Γ Φ ψ ↦ f Γ Φ Γ Φ ψ

/-- The kit of the constructors. -/
def ctorKit (P : Prog) (S : Defs) (T : Defs3) (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
  let W := kwKit P S T ix E 2 [true, true] "Reader.kwCons"
  let W₁ := kwKit P S T ix E 2 [true, true] "Ctor.of"
  let W₂ := kwKit P S T ix E 2 [true, true] "Ctor.as"
  let W₃ := kwKit P S T ix E 1 [true] "Reader.kwNil"
  let K₀ := denKit P S ix E
  { K₀ with
    P := { K₀.P with folded := K₀.P.folded.filter (· != "Typing.ctorOk") }
    more := (K₀.more ++ W.K.more ++ W₁.K.more ++ W₂.K.more ++ W₃.K.more ++
      ["lcaseRebuild", "lcaseRebuildL"].filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size).eraseDups }

/-- The stage functions' equations at the coercions of a value to its type and of a value to a
datatype. -/
def castEqs (P : Prog) (T : Defs3) : List Step :=
  let P' := { walkProg P with folded := (walkProg P).folded ++ ["Typing.decimalChars"] }
  kwEqs P' T "Ctor.of" 2 (pc P "Typing.tOf" [v 1, v 0]) true ++
    kwEqs P' T "Ctor.as" 2 (pc P "Typing.tAs" [v 1, v 0]) true

/-- The first component of the typing's fold at a form: the form as the typing rebuilds it. -/
def rawT (T : Defs3) (Ev f : Term) : Term :=
  Term.fst (Term.app (Term.snd (T.foldAt 1 [Ev] f)) Term.star)

/-- A coercion of a value to its type has a type: the value has a type, equal to that the annotation
reads, whose erasure is the coercion's. In the context of the value, the annotation, the context
and the typing environment. -/
def ofTyped (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("ofTyped", fun ix E ↦ do
    let K := ctorKit P S T ix E
    let P := K.P
    let o := P.o
    let conj := Internal.Logic.conj o
    let Γ := [treeTy, treeTy, list treeTy, T.envTy]
    let (x, f, cx, Ev) := (v 0, v 1, v 2, v 3)
    let syn (t : Term) : Term := pc P "Typing.synIn" [Ev, cx, t]
    let of := pc P "Typing.tOf" [f, x]
    let read := pc P "Typing.readTy" [Ev, rawT T Ev f]
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let thm : Internal.Thm := ⟨0, Γ, [isSomeT (syn of)], conj (isSomeT read) (conj (isSomeT (syn x))
      (conj (truth o (pc P "Typing.sameTy" [getT read, getT (syn x)]))
        (Term.eq (getT (syn of)) (pc P "Typing.eraseTy" [getT read]))))⟩
    let (xAt, fAt, cxAt, EAt) := (atPos 3, atPos 2, atPos 1, atPos 0)
    let synAt (t : List Tree → Term) (Γ : List Tree) : Term :=
      pc P "Typing.synIn" [EAt Γ, cxAt Γ, t Γ]
    let readAt (Γ : List Tree) : Term := pc P "Typing.readTy" [EAt Γ, rawT T (EAt Γ) (fAt Γ)]
    let main : Deducer :=
      decideOpt K readAt (linkK K "ofTyped: no annotation" (K.hypFalse 0)) <|
      decideOpt K (synAt xAt) (linkK K "ofTyped: no type" (K.hypFalse 0)) <|
      decideIn K (fun Γ ↦ pc P "Typing.sameTy" [getT (readAt Γ), getT (synAt xAt Γ)])
        (linkK K "ofTyped: unequal" (K.hypFalse 0)) <|
      linkK K "ofTyped: the parts" (K.solve 6)
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "ofTyped: not proved" fun _ ↦ none
    pure (thm, d))

/-- The typing's type of lists of trees. -/
def listOfTrees (P : Prog) : Term := pc P "Typing.tyList" [pc P "Typing.tyT" []]

/-- The writer's construction of a list from a coerced head. -/
def consOfForm (P : Prog) (f x r : Term) : Term :=
  listNode [kwAtom P "Reader.kwCons", pc P "Typing.tOf" [f, x], r]

/-- A construction of a list of trees: the head's type the trees, the rest's that of the list. In
the context of the rest, the head's value and annotation, the context and the typing environment.
-/
def consTyped (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("consTyped", fun ix E ↦ do
    let K := ctorKit P S T ix E
    let P := K.P
    let o := P.o
    let conj := Internal.Logic.conj o
    let Γ := [treeTy, treeTy, treeTy, list treeTy, T.envTy]
    let (r, x, f, cx, Ev) := (v 0, v 1, v 2, v 3, v 4)
    let syn (t : Term) : Term := pc P "Typing.synIn" [Ev, cx, t]
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let of := pc P "Typing.tOf" [f, x]
    let form := consOfForm P f x r
    let tyT := pc P "Typing.tyT" []
    let thm : Internal.Thm := ⟨0, Γ,
      [isSomeT (syn form), Term.eq (getT (syn form)) (listOfTrees P)],
      conj (isSomeT (syn r)) (conj (Term.eq (getT (syn r)) (listOfTrees P))
        (conj (isSomeT (syn of)) (Term.eq (getT (syn of)) tyT)))⟩
    let (rAt, xAt, fAt, cxAt, EAt) := (atPos 4, atPos 3, atPos 2, atPos 1, atPos 0)
    let synAt (t : List Tree → Term) (Γ : List Tree) : Term :=
      pc P "Typing.synIn" [EAt Γ, cxAt Γ, t Γ]
    let ofAt (Γ : List Tree) : Term := pc P "Typing.tOf" [fAt Γ, xAt Γ]
    let childT := (primT Kernel.Prim.child).getD Term.star
    let main : Deducer :=
      decideOpt K (synAt ofAt) (linkK K "consTyped: no head" (K.hypFalse 0)) <|
      decideOpt K (synAt rAt) (linkK K "consTyped: no rest" (K.hypFalse 0)) <|
      decideIn K (fun Γ ↦ pc P "Typing.sameTy" [pc P "Typing.tyList" [getT (synAt ofAt Γ)],
          getT (synAt rAt Γ)])
        (linkK K "consTyped: unequal" (K.hypFalse 0)) <|
      K.cutThm "equalSound" (fun Γ ↦ [pc P "Typing.tyList" [getT (synAt ofAt Γ)]]) <|
      K.allEΓ (fun Γ ↦ getT (synAt rAt Γ)) <|
      K.impE (linkK K "consTyped: the test" (K.solve 3)) <|
      fun Γ Φ ψ ↦
      let hE := Φ.length - 1
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 1) .full) 1 (
        K.image hE (fun t ↦ apps childT [t, leafT bnilT]) (normLastK K <|
          linkK K "consTyped: the parts" (K.solve 6))) Γ Φ ψ
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "consTyped: not proved" fun _ ↦ none
    pure (thm, d))

/-- A value related at a type whose erasure is the trees is a quotation: the type a node, its label
decided by the test, the relation unfolded at each of the trees, the datatypes and the sorts. In
the context of the value, the type and the relation's context. -/
def relQuoted (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relQuoted", fun ix E ↦ do
    let K := ctorKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let Γ := [treeTy, treeTy, Defs3.ctxTy]
    let eqT ← primT Kernel.Prim.eq
    let thm : Internal.Thm := ⟨0, Γ,
      [truth o (apps eqT [leafT (call D.lab [] [pc P "Typing.eraseTy" [v 1]]), leafT bnilT]),
        Term.app (T.relT (v 2) (v 1)) (v 0)],
      Internal.Logic.ex o treeTy (Term.lam treeTy (Term.eq (v 1) (quoteV P (v 0))))⟩
    -- the relation unfolded and split: falsity, a tree's quotation, a member's
    let opened : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 1 ++ [.delta T.q]) .full) 1 (fun Γ Φ ψ ↦
        let hR := Φ.length - 1
        K.splitHyp hR (fun Γ Φ ψ ↦
          ((K.hypFalse hR) Γ Φ ψ).orElse fun _ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ hR) .full) hR
            (fun Γ Φ ψ ↦
            K.exE (fun Γ Φ ψ ↦
              let tAt := atPos (Γ.length - 1)
              ((normLastK K (dExI L K.G K.E (tAt Γ) (K.solve 3))) Γ Φ ψ).orElse fun _ ↦
                K.conjE (fun Γ Φ ψ ↦
                  dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 2)) .full) (Φ.length - 2)
                    (dExI L K.G K.E (tAt Γ) (K.solve 3)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) 8 Γ Φ ψ) Γ Φ ψ
    let some d := (K.treeNode (v 1) (K.splitHyp 0
        (linkK K "relQuoted: the relation" opened) 8)) thm.ctx thm.hyps thm.concl
      | dbgTrace "relQuoted: not proved" fun _ ↦ none
    pure (thm, d))

/-- That an atom names nothing but a binder: no definition of the typing environment, no primitive
and not the unit value. -/
def atomFreeT (P : Prog) (Ev a : Term) : List Term :=
  let o := P.o
  let n := atomNameT a
  [notTest o (pc P "Prelude.isSome" [pc P "Typing.lookupName" [n, pc P "Typing.envDefs" [Ev]]]),
    notTest o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [n, pc P "Reader.primNames" []]]),
    notTest o (pc P "Reader.named" [a, pc P "Reader.kwUnitValue" []])]

/-- An atom no numeral, naming no abbreviation and nothing but a binder, with a type, names a binder
of the context, whose type it has: each of the typing's tests at an atom decided in its order,
refuting the type or by the hypotheses. In the context of the characters, the context and the
typing environment. -/
def atomTyped (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("atomTyped", fun ix E ↦ do
    let K₀ := ctorKit P S T ix E
    let K : Kit := { K₀ with P := { K₀.P with folded :=
      (K₀.P.folded.filter (· != "Typing.synAtom")) ++ ["Typing.keywordTx"] } }
    let P := K.P
    let L := K.L
    let o := P.o
    let vars := [list treeTy, list treeTy, T.envTy]
    let at_ := denAt vars
    let (Ev, cx, cs) := (at_ 6, at_ 7, at_ 8)
    let form := nodeT (Term.pair (numeral 1) cs)
    let n := atomNameT form
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let lookup := pc P "Typing.lookupName" [n, cx]
    let syn := pc P "Typing.synIn" [Ev, cx, form]
    let hyps : List Term := [T.numsT Ev (at_ 1),
      notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [n, at_ 1]])] ++
      atomFreeT P Ev form ++
      [Term.eq (pc P "Reader.numeral" [cs]) (pc P "Prelude.none" []), isSomeT syn]
    let hNum := hyps.length - 2
    let hSyn := hyps.length - 1
    let thm : Internal.Thm := ⟨0, denCtx vars, hyps,
      Internal.Logic.conj o (notTest o (boundNameT P n))
        (Internal.Logic.conj o (isSomeT lookup) (Term.eq (getT syn) (getT lookup)))⟩
    let (EAt, cxAt, csAt) := (atPos 6, atPos 7, atPos 8)
    let aAt (Γ : List Tree) : Term := nodeT (Term.pair (numeral 1) (csAt Γ))
    let nAt (Γ : List Tree) : Term := atomNameT (aAt Γ)
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let refuted (h : ℕ) : Deducer := dImpE L h (K.solve 3) lastFalse
    let lookupIn (xs : List Tree → Term) (Γ : List Tree) : Term :=
      pc P "Prelude.isSome" [pc P "Typing.lookupName" [nAt Γ, xs Γ]]
    let numsFalse : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) 0 (fun Γ Φ ψ ↦
        dAllE L K.G K.E (Φ.length - 1) (nAt Γ) (K.conjE <| fun Γ Φ ψ ↦
          dImpE L (Φ.length - 2) (K.solve 3) (K.exE <| K.conjE fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 2)) .full) (Φ.length - 2)
              (refuted 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let main : Deducer :=
      dRwHyp (evalRw K.G K.E [] .full) hNum <|
      decideIn K (fun Γ ↦ pc P "Typing.keywordTx" [aAt Γ])
        (decideIn K (fun Γ ↦ boundNameT P (nAt Γ))
          (decideIn K (fun Γ ↦ pc P "Typing.hasName" [nAt Γ, pc P "Typing.envNums" [EAt Γ]])
            (decideIn K (lookupIn cxAt)
              (decideIn K (lookupIn (fun Γ ↦ pc P "Typing.envDefs" [EAt Γ]))
                (decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf"
                    [nAt Γ, pc P "Reader.primNames" []]])
                  (decideIn K (fun Γ ↦ pc P "Reader.named" [aAt Γ, pc P "Reader.kwUnitValue" []])
                    (linkK K "atomTyped: no type" (K.hypFalse hSyn))
                    (linkK K "atomTyped: the unit" (refuted 4)))
                  (linkK K "atomTyped: a primitive" (refuted 3)))
                (linkK K "atomTyped: a definition" (refuted 2)))
              (linkK K "atomTyped: the binder" <| K.norm <| dConjI L (dImpI L lastFalse)
                (K.solve 4)))
            (linkK K "atomTyped: a numeral abbreviation" numsFalse))
          (linkK K "atomTyped: a bound name" (K.hypFalse hSyn)))
        (linkK K "atomTyped: a keyword" (K.hypFalse hSyn))
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "atomTyped: not proved" fun _ ↦ none
    pure (thm, d))

/-- The erasure of an atom is the atom: the fold's equation at an atom. In the context of the
characters. -/
def eraseAtom (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("eraseAtom", fun ix E ↦ do
    let K := ctorKit P S T ix E
    let form := nodeT (Term.pair (numeral 1) (v 0))
    let thm : Internal.Thm := ⟨0, [list treeTy], [],
      Term.eq (pc K.P "Datatype.eraseExpr" [form]) form⟩
    let some d := linkK K "eraseAtom" K.byNorm thm.ctx thm.hyps thm.concl
      | dbgTrace "eraseAtom: not proved" fun _ ↦ none
    pure (thm, d))

/-- The list value of a head and a rest. -/
def consV (x w : Term) : Term := kNode Kernel.Label.cons [x, w]

/-- The writer's construction of a list from expressions denoting a value and a list value denotes
the list value of the head and the rest. -/
def denConsV (P : Prog) : DenRule :=
  let vars := [treeTy, treeTy, treeTy, treeTy]
  let at_ := denAt vars
  let (e, l, x, w) := (at_ 6, at_ 7, at_ 8, at_ 9)
  { name := "denConsV", vars, plain := [pc P "Recognize.rCons" []],
    subs := [sub e x, sub l w],
    form := pc P "Recognize.s3" [pc P "Recognize.rCons" [], e, l],
    value := consV x w, levels := 1 }

/-- The writer's application of the node primitive to an expression denoting a quotation and to one
denoting a list value of quotations denotes the quotation of the node. -/
def denNodeL (P : Prog) : DenRule :=
  let vars := [list treeTy, treeTy, treeTy, treeTy, treeTy]
  let at_ := denAt vars
  let (e, l, t, w, xs) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10)
  let a := pc P "Recognize.rNode" []
  let listV := pc P "Eval.listOf" [w]
  { name := "denNodeL", vars, absent := [a], plain := [a],
    more := [truth P.o (pc P "Prelude.isSome" [listV]),
      Term.eq (call D.children [] [pc P "Prelude.get" [listV]]) (quotesT P xs)],
    subs := [sub e (quoteV P t), sub l w],
    form := pc P "Recognize.s3" [a, e, l],
    value := quoteV P (nodeT (Term.pair (call D.lab [] [t]) xs)), levels := 2,
    pre := fun K up k ↦ decideIn K (up (pc P "Prelude.isSome" [listV])) (K.hypFalse 3) k,
    rules := ["unquotesOf"] }

/-- The right fold of the writer's list of a constructor's fields, from the end's form, the number
of the fields and the fold's count of those after each. -/
def listFold (P : Prog) (nf z fs : Term) : Term :=
  let C := prod treeTy treeTy
  let addT := (primT Kernel.Prim.add).getD Term.star
  let subT := (primT Kernel.Prim.sub).getD Term.star
  foldrT treeTy C (Term.lam treeTy (Term.lam C (Term.pair
      (apps addT [Term.fst (v 0), leafT (numeral 1)])
      (consOfForm P (v 1) (fieldAtomT P (apps subT [apps subT [sh 2 nf, leafT (numeral 1)],
        Term.fst (v 0)])) (Term.snd (v 0))))))
    (Term.pair (leafT bnilT) z) fs

/-- The representations of a constructor's field types with the abbreviations of the declarations
{lit}`dv` expanded, as the marker holds them. -/
def repsT (P : Prog) (dv fs : Term) : Term :=
  let Ls := list treeTy
  foldrT treeTy Ls (Term.lam treeTy (Term.lam Ls (consT treeTy
    (pc P "Datatype.expandAliases" [sh 2 dv, v 1]) (v 0)))) (nilT treeTy) fs

/-- That a value of a field type holds of the marker's reading of the type: at every tree whose
quotation the relation relates to the type the typing reads, the marker's test of the type at the
tree's memberships. In the context of the type. -/
def cohT (P : Prog) (T : Defs3) (R Ev dv F : Term) : Term :=
  let o := P.o
  let A := pc P "Prelude.get" [pc P "Typing.readTy" [Ev, rawT T Ev F]]
  Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
    (Term.app (T.relT (sh 1 R) (sh 1 A)) (quoteV P (v 0)))
    (truth o (pc P "Typing.fieldOk" [Term.snd (sh 1 R),
      pc P "Datatype.expandAliases" [sh 1 dv, sh 1 F],
      pc P "Typing.memberships" [Term.snd (sh 1 R), v 0]]))))

/-- That the atoms of a constructor's fields, at every number, name no abbreviation, are fixed by
the expansion of the numeral abbreviations, and name nothing but a binder. -/
def fieldAllT (P : Prog) (Ev nums : Term) : Term :=
  let o := P.o
  let k := v 0
  let a := fieldAtomT P k
  let (Ev', nums') := (sh 1 Ev, sh 1 nums)
  let fn := Term.lam treeTy (pc P "Reader.expandNums" [sh 2 nums, v 0])
  let parts : List Term :=
    [notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT a, nums']]),
      truth o (pc P "charsFixed" [fn, pc P "Typing.decimalChars" [k]])] ++ atomFreeT P Ev' a
  Internal.Logic.all o treeTy (Term.lam treeTy
    (parts.dropLast.foldr (Internal.Logic.conj o) (parts.getLastD Term.star)))

/-- That an expression denotes a list value of the quotations of trees of which the walk of a
constructor's fields holds. -/
def listEndT (P : Prog) (S : Defs) (Dv nums names tys cx env ms flag rty fts e : Term) : Term :=
  let o := P.o
  let Ls := list treeTy
  let up (t : Term) : Term := sh 2 t
  let listV := pc P "Eval.listOf" [v 0]
  Internal.Logic.ex o Ls (Term.lam Ls (Internal.Logic.ex o treeTy (Term.lam treeTy
    (Internal.Logic.conj o
      (denT P S (up Dv) (up tys) (up names) (up nums) (up (scopeOf P nums cx)) (up env) (up e)
        (v 0))
      (Internal.Logic.conj o (truth o (pc P "Prelude.isSome" [listV])) (Internal.Logic.conj o
        (Term.eq (call D.children [] [pc P "Prelude.get" [listV]]) (quotesT P (v 1)))
        (truth o (walkT P (up ms) (up flag) (up rty) (up fts)
          (membershipsT P (up ms) (v 1))))))))))

/-- The context of the writer's list of a constructor's fields. -/
def listVars (T : Defs3) : List Tree :=
  let Tt := treeTy
  let Ls := list treeTy
  [Ls, Tt, Tt, Tt, Tt, Ls, Ls, T.envTy]

/-- The writer's list of a constructor's fields, typed at the list of trees, denotes the list value
of the quotations of trees of which the walk of the marker's fields holds: by induction on the
fields, the end given. A construction: the typing's parts ({name}`consTyped`, {name}`ofTyped`,
{name}`atomTyped`), the field's value ({name}`fieldVarRel`) related at the annotation, whose erasure
is the trees, so a quotation ({name}`relQuoted`), holding of the marker's type. -/
def ctorList (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("ctorList", fun ix E ↦ do
    let K := ctorKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let imp := Internal.Logic.imp o
    let Ls := list treeTy
    let vars := listVars T
    let at_ := denAt vars
    let Γ₀ := denCtx vars
    let (Ev, cx, dv, nf, z, flag, rty, fs) :=
      (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11, at_ 12, at_ 13)
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let synOf (Ev cx t : Term) : Term := pc P "Typing.synIn" [Ev, cx, t]
    let eraseT (t : Term) : Term := pc P "Datatype.eraseExpr" [t]
    let Lz (fs : Term) : Term := Term.snd (listFold P nf z fs)
    let endOf := listEndT P S
    let ms := Term.snd (at_ 0)
    let base : Term := imp (isSomeT (synOf Ev cx z))
      (imp (Term.eq (getT (synOf Ev cx z)) (listOfTrees P))
        (endOf (at_ 0) (at_ 1) (at_ 2) (at_ 3) cx (at_ 5) ms flag rty (nilT treeTy) (eraseT z)))
    let hyps : List Term := [T.numsT Ev (at_ 1), T.envT (at_ 0) cx (at_ 5), fieldAllT P Ev (at_ 1),
      notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev"
        [atomNameT (pc P "Recognize.rCons" []), at_ 1]]), base]
    let cohs (fs : Term) : Term :=
      S.allL (Term.lam treeTy (cohT P T (sh 1 (at_ 0)) (sh 1 Ev) (sh 1 dv) (v 0))) fs
    let φ := imp (cohs fs) (imp (isSomeT (synOf Ev cx (Lz fs)))
      (imp (Term.eq (getT (synOf Ev cx (Lz fs))) (listOfTrees P))
        (endOf (at_ 0) (at_ 1) (at_ 2) (at_ 3) cx (at_ 5) ms flag rty (repsT P dv fs)
          (eraseT (Lz fs)))))
    let some lowered := Internal.lowerHyps P.G 0 Γ₀.tail hyps
      | dbgTrace "ctorList: the hypotheses" fun _ ↦ none
    let (EAt, cxAt, dvAt, nfAt, zAt) := (atPos 6, atPos 7, atPos 8, atPos 9, atPos 10)
    let msAt (Γ : List Tree) : Term := Term.snd (atPos 0 Γ)
    let scopeAt (Γ : List Tree) : Term := scopeOf P (atPos 1 Γ) (cxAt Γ)
    let fixedAt (Γ : List Tree) : List Term :=
      [atPos 5 Γ, scopeAt Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
    let LzAt (Γ : List Tree) (fs : Term) : Term := Term.snd (listFold P (nfAt Γ) (zAt Γ) fs)
    -- no fields: the end given
    let d₀ ← (linkK K "ctorList: empty" <| dImpI L <| dImpI L <| dImpI L fun Γ Φ ψ ↦
      let (hS, hE) := (Φ.length - 2, Φ.length - 1)
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ hE) .full) hE (dImpE L 4 (K.byHyp hS) <|
        K.impE (linkK K "ctorList: the end's type" K.byNorm) <| K.exE <| K.exE <| K.conjE <|
        K.conjE <| K.conjE fun Γ Φ ψ ↦
          let (tsAt, wAt) := (atPos (Γ.length - 2), atPos (Γ.length - 1))
          let n := Φ.length
          dExI L K.G K.E (tsAt Γ) (dExI L K.G K.E (wAt Γ) (dConjI L
            (linkK K "ctorList: the end" (applyThm K "denCong" (fun Γ ↦
                [wAt Γ, eraseT (zAt Γ), eraseT (LzAt Γ (nilT treeTy))] ++ fixedAt Γ)
              [K.byNorm, dHyp] dHyp))
            (dConjI L (K.byHyp (n - 4)) (dConjI L
              (linkK K "ctorList: the end's trees" (dRwHyp (evalRw K.G K.E (K.rulesEx Φ (n - 2))
                .full) (n - 2) K.byNorm))
              (linkK K "ctorList: the end's walk" (K.byHyp (n - 1))))))) Γ Φ ψ) Γ Φ ψ)
      Γ₀.tail lowered (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let (fAt, tlAt) := (atPos 13, atPos 14)
    let ih := hyps.length
    let kAt (Γ : List Tree) : Term :=
      let subT := (primT Kernel.Prim.sub).getD Term.star
      apps subT [apps subT [nfAt Γ, leafT (numeral 1)],
        Term.fst (listFold P (nfAt Γ) (zAt Γ) (tlAt Γ))]
    let xAt (Γ : List Tree) : Term := fieldAtomT P (kAt Γ)
    let rAt (Γ : List Tree) : Term := LzAt Γ (tlAt Γ)
    let readAt (Γ : List Tree) : Term :=
      getT (pc P "Typing.readTy" [EAt Γ, rawT T (EAt Γ) (fAt Γ)])
    let synX (Γ : List Tree) : Term := getT (synOf (EAt Γ) (cxAt Γ) (xAt Γ))
    let normH (h : ℕ) (k : Deducer) : Deducer := withCtx fun _ Φ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h k
    let lastIdx (k : ℕ → Deducer) : Deducer := withCtx fun _ Φ ↦ k (Φ.length - 1)
    -- the field's quotation in the list, its test and the rest's walk
    let finish (tAt tsAt wrAt : List Tree → Term) (hOk hLs hEq hWalk : ℕ) : Deducer :=
      let qt (Γ : List Tree) : Term := quoteV P (tAt Γ)
      let lF (Γ : List Tree) : Term := eraseT (rAt Γ)
      let formAt (Γ : List Tree) : Term := pc P "Recognize.s3"
        [pc P "Recognize.rCons" [], xAt Γ, lF Γ]
      let valAt (Γ : List Tree) : Term := consV (qt Γ) (wrAt Γ)
      let okAt (Γ : List Tree) : Term := pc P "Typing.fieldOk" [msAt Γ,
        pc P "Datatype.expandAliases" [dvAt Γ, fAt Γ], pc P "Typing.memberships" [msAt Γ, tAt Γ]]
      let listAt (Γ : List Tree) : Term := pc P "Prelude.isSome" [pc P "Eval.listOf" [wrAt Γ]]
      applyThm K "denConsV" (fun Γ ↦ [wrAt Γ, qt Γ, lF Γ, xAt Γ] ++ fixedAt Γ)
        [K.byHyp 3, dHyp, dHyp] <|
      K.cutThm "eraseAtom" (fun Γ ↦ [fieldChars P (kAt Γ)]) <| normLastK K <|
      normH hEq <|
      withCtx fun Γ _ ↦ dExI L K.G K.E (consT treeTy (tAt Γ) (tsAt Γ))
        (dExI L K.G K.E (valAt Γ) (dConjI L
        (linkK K "ctorList: the list" (applyThm K "denCong" (fun Γ ↦ [valAt Γ, formAt Γ,
            eraseT (LzAt Γ (consT treeTy (fAt Γ) (tlAt Γ)))] ++ fixedAt Γ)
          [linkK K "ctorList: the list's form" K.byNorm, dHyp] dHyp))
        (decideIn K listAt (K.hypFalse hLs) <| dConjI L
          (linkK K "ctorList: a list" (K.solve 3)) <| dConjI L
          (linkK K "ctorList: the trees" K.byNorm)
          (linkK K "ctorList: the walk" (decideIn K okAt (K.hypFalse hOk) (K.byHyp hWalk))))))
    -- the field's value related at the annotation, a quotation
    let related (tsAt wrAt : List Tree → Term) (hLs hEq hWalk hCh dW rW hSame hOf hOe hTy : ℕ)
        (wAt : List Tree → Term) : Deducer :=
      K.cutThm "equalSound" (fun Γ ↦ [readAt Γ]) <| K.allEΓ synX <| K.impE (K.byHyp hSame) <|
      lastIdx fun e₁ ↦ normH hTy <| normH e₁ <| normH hOf <| normH hOe <|
      linkK K "ctorList: the field's relation" <|
      applyThm K "relQuoted" (fun Γ ↦ [wAt Γ, readAt Γ, atPos 0 Γ])
        [linkK K "ctorList: the erasure" (K.solve 3), K.byHyp rW] <|
      K.exE <| normLastK K <| withCtx fun Γ _ ↦
      let tAt := atPos (Γ.length - 1)
      dAllE L K.G K.E hCh (tAt Γ) <| K.impE (K.byHyp rW) <| lastIdx fun hOk ↦
      applyThm K "denVal" (fun Γ ↦ [wAt Γ, quoteV P (tAt Γ), xAt Γ] ++ fixedAt Γ)
        [linkK K "ctorList: the quotation" K.byNorm, K.byHyp dW] <|
      finish tAt tsAt wrAt hOk hLs hEq hWalk
    let cons : Deducer := dImpI L <| dImpI L <| dImpI L <| withCtx fun _ Φ₁ ↦
      let (hC, hS, hE) := (Φ₁.length - 3, Φ₁.length - 2, Φ₁.length - 1)
      normH hC <| K.conjE <| withCtx fun _ Φ₂ ↦
      let (hCh, hCt) := (Φ₂.length - 2, Φ₂.length - 1)
      normH hE <|
      applyThm K "consTyped" (fun Γ ↦ [rAt Γ, xAt Γ, fAt Γ, cxAt Γ, EAt Γ])
        [K.byHyp hS, linkK K "ctorList: the construction's type" K.byNorm] <|
      K.conjE <| K.conjE <| K.conjE <| withCtx fun _ Φ₃ ↦
      let n := Φ₃.length
      let (hRs, hRe, hOs, hOe) := (n - 6, n - 4, n - 2, n - 1)
      normH hRe <|
      dImpE L ih (K.byHyp hCt) <| K.impE (K.byHyp hRs) <|
      K.impE (linkK K "ctorList: the rest's type" K.byNorm) <|
      K.exE <| K.exE <| K.conjE <| K.conjE <| K.conjE <| withCtx fun Γ₄ Φ₄ ↦
      let (tsAt, wrAt) := (atPos (Γ₄.length - 2), atPos (Γ₄.length - 1))
      let (hLs, hEq, hWalk) := (Φ₄.length - 4, Φ₄.length - 2, Φ₄.length - 1)
      applyThm K "ofTyped" (fun Γ ↦ [xAt Γ, fAt Γ, cxAt Γ, EAt Γ]) [K.byHyp hOs] <|
      K.conjE <| K.conjE <| K.conjE <| withCtx fun _ Φ₅ ↦
      let m := Φ₅.length
      let (hXs, hSame, hOf) := (m - 4, m - 2, m - 1)
      withCtx fun Γ _ ↦ dAllE L K.G K.E 2 (kAt Γ) <| K.conjE <| K.conjE <| K.conjE <| K.conjE <|
      withCtx fun _ Φ₆ ↦
      let o₆ := Φ₆.length
      let (hPlain, hFixed, hF1, hF2, hF3) := (o₆ - 8, o₆ - 6, o₆ - 4, o₆ - 2, o₆ - 1)
      K.cutThm "fieldNotNumeral" (fun Γ ↦ [kAt Γ]) <| normLastK K <|
      applyThm K "atomTyped" (fun Γ ↦ [fieldChars P (kAt Γ), cxAt Γ, EAt Γ] ++ fixedAt Γ)
        [K.byHyp 0, K.byHyp hPlain, K.byHyp hF1, K.byHyp hF2, K.byHyp hF3,
          linkK K "ctorList: not a numeral" K.byNorm, K.byHyp hXs] <|
      K.conjE <| K.conjE <| withCtx fun _ Φ₇ ↦
      let p := Φ₇.length
      let (hNB, hLk, hTy) := (p - 4, p - 2, p - 1)
      applyThm K "fieldVarRel" (fun Γ ↦ [kAt Γ, cxAt Γ, EAt Γ] ++ fixedAt Γ)
        [K.byHyp 0, K.byHyp 1, K.byHyp hPlain, K.byHyp hFixed, K.byHyp hNB, K.byHyp hLk] <|
      K.exE <| K.conjE <| withCtx fun Γ₈ Φ₈ ↦
      related tsAt wrAt hLs hEq hWalk hCh (Φ₈.length - 2) (Φ₈.length - 1) hSame hOf hOe hTy
        (atPos (Γ₈.length - 1))
    let d₁ ← linkK K "ctorList: construction" cons (Ls :: treeTy :: Γ₀.tail)
      (lowered.map Internal.weaken2 ++ [Internal.weakenElem φ]) (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ₀, hyps, φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The development of the constructors. -/
def constructorDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [denRule P S T (denFieldVar P), fieldNotNumeral P S, fieldVarRel P S T,
      denRule P S T (denRestVar P), restVarRel P S T] ++ castEqs P T ++
    [ofTyped P S T, consTyped P S T, relQuoted P S T, atomTyped P S T,
      eraseAtom P S T, denRule P S T (denConsV P), denRule P S T (denNodeL P), ctorList P S T]

/-- The development of {name}`constructorDev`, after the recognizers', stored as the certificate
{lit}`datatype-constructor`. -/
def constructorCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := walkAfter P S T | throw "the base is not stated"
  certifyAfter P (names ++ (walkDev P S T).map (·.1) ++ (recognizerDev P S T).map (·.1) ++
    (recognizerFoldDev P S T).map (·.1)) "datatype-constructor" (constructorDev P S T) before

/-- A type whose erasure is a type of lists is one, the erasure of its elements' the first child of
its erasure: the type a node, its label decided by the hypothesis. In the context of the type. -/
def eraseTyList (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("eraseTyList", fun ix E ↦ do
    let K := ctorKit P S T ix E
    let P := K.P
    let o := P.o
    let eqT ← primT Kernel.Prim.eq
    let childT ← primT Kernel.Prim.child
    let four := leafT (numeral 4)
    let labOf (t : Term) : Term := leafT (call D.lab [] [t])
    let er (t : Term) : Term := pc P "Typing.eraseTy" [t]
    let first (t : Term) : Term := apps childT [t, leafT bnilT]
    let thm : Internal.Thm := ⟨0, [treeTy], [truth o (apps eqT [labOf (er (v 0)), four])],
      Internal.Logic.conj o (truth o (apps eqT [labOf (v 0), four]))
        (Term.eq (er (first (v 0))) (first (er (v 0))))⟩
    let some d := (K.treeNode (v 0) (fun Γ₀ Φ₀ ψ₀ ↦
        let csAt := atPos (Γ₀.length - 1)
        K.splitHyp 0 (fun Γ Φ ψ ↦
          K.listCase treeTy (csAt Γ) (linkK K "eraseTyList: no children" (K.solve 4))
            (linkK K "eraseTyList: the type of lists" (K.solve 4)) Γ Φ ψ) 8 Γ₀ Φ₀ ψ₀))
        thm.ctx thm.hyps thm.concl
      | dbgTrace "eraseTyList: not proved" fun _ ↦ none
    pure (thm, d))

/-- A value related at a type of the label of lists is a list value of elements related at the
first child of the type: the type a node, its label decided, the relation unfolded. In the context
of the value, the type and the relation's context. -/
def relListOf (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relListOf", fun ix E ↦ do
    let K := ctorKit P S T ix E
    let P := K.P
    let o := P.o
    let eqT ← primT Kernel.Prim.eq
    let childT ← primT Kernel.Prim.child
    let Γ := [treeTy, treeTy, Defs3.ctxTy]
    let listV := pc P "Eval.listOf" [v 0]
    let thm : Internal.Thm := ⟨0, Γ,
      [truth o (apps eqT [leafT (call D.lab [] [v 1]), leafT (numeral 4)]),
        Term.app (T.relT (v 2) (v 1)) (v 0)],
      Internal.Logic.conj o (truth o (pc P "Prelude.isSome" [listV]))
        (S.allL (Term.lam treeTy (Term.app (T.relT (v 3) (apps childT [v 2, leafT bnilT])) (v 0)))
          (call D.children [] [pc P "Prelude.get" [listV]]))⟩
    let unfoldR (Φ : List Term) : List Internal.NormRule := K.rulesEx Φ 1 ++ [.delta T.q]
    let some d := (K.treeNode (v 1) (fun Γ₀ Φ₀ ψ₀ ↦
        let csAt := atPos (Γ₀.length - 1)
        K.splitHyp 0 (fun Γ Φ ψ ↦
          K.listCase treeTy (csAt Γ)
            (linkK K "relListOf: no children" fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (unfoldR Φ) .full) 1 (K.conjE fun Γ Φ ψ ↦
                let (hL, hA) := (Φ.length - 2, Φ.length - 1)
                let vsAt (Γ : List Tree) : Term := call D.children []
                  [pc P "Prelude.get" [pc P "Eval.listOf" [atPos 2 Γ]]]
                let Q (Γ : List Tree) : Term := Term.lam treeTy (Term.app
                  (T.relT (sh 1 (atPos 0 Γ)) (apps childT [sh 1 (atPos 1 Γ), leafT bnilT])) (v 0))
                K.norm (dConjI K.L (K.byHyp hL)
                  (K.cutThm "allMono" (fun Γ ↦ [vsAt Γ]) <|
                    K.allEΓ (fun _ ↦ Term.lam treeTy (Internal.Logic.ff o)) <| K.allEΓ Q <|
                    K.impE (K.byHyp hA) <|
                    K.impE (dAllI K.L <| dImpI K.L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) <|
                    fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ)
            (linkK K "relListOf: the elements" fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (unfoldR Φ) .full) 1 (fun Γ Φ ψ ↦
                dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta T.q]) .full) dHyp Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
            8 Γ₀ Φ₀ ψ₀))
        thm.ctx thm.hyps thm.concl
      | dbgTrace "relListOf: not proved" fun _ ↦ none
    pure (thm, d))

/-- A list value's elements related at a type whose erasure is the trees are the quotations of
trees of which the walk of a variable field holds: by induction on the elements, each a quotation
({name}`relQuoted`) holding of the field's type by the hypothesis. In the context of the elements,
the type, the marker's type of the field and the relation's context. -/
def restQuotes (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("restQuotes", fun ix E ↦ do
    let K := ctorKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let imp := Internal.Logic.imp o
    let Ls := list treeTy
    let eqT ← primT Kernel.Prim.eq
    let Γ₀ := [Ls, treeTy, treeTy, Defs3.ctxTy]
    let (vs, A, rty, R) := (v 0, v 1, v 2, v 3)
    let hyps : List Term :=
      [truth o (apps eqT [leafT (call D.lab [] [pc P "Typing.eraseTy" [A]]), leafT bnilT]),
        Internal.Logic.all o treeTy (Term.lam treeTy (imp
          (Term.app (T.relT (sh 1 R) (sh 1 A)) (quoteV P (v 0)))
          (truth o (pc P "Typing.fieldOk" [Term.snd (sh 1 R), sh 1 rty,
            pc P "Typing.memberships" [Term.snd (sh 1 R), v 0]]))))]
    let one := leafT (numeral 1)
    let φ := imp (S.allL (Term.lam treeTy (Term.app (T.relT (sh 1 R) (sh 1 A)) (v 0))) vs)
      (Internal.Logic.ex o Ls (Term.lam Ls (Internal.Logic.conj o
        (Term.eq (sh 1 vs) (quotesT P (v 0)))
        (truth o (walkT P (Term.snd (sh 1 R)) one (sh 1 rty) (nilT treeTy)
          (membershipsT P (Term.snd (sh 1 R)) (v 0)))))))
    let some lowered := Internal.lowerHyps P.G 0 Γ₀.tail hyps
      | dbgTrace "restQuotes: the hypotheses" fun _ ↦ none
    let (RAt, rtyAt, AAt, hAt) := (atPos 0, atPos 1, atPos 2, atPos 3)
    let d₀ ← (dImpI L fun Γ Φ ψ ↦ dExI L K.G K.E (nilT treeTy) (K.solve 4) Γ Φ ψ) Γ₀.tail lowered
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let lastIdx (k : ℕ → Deducer) : Deducer := withCtx fun _ Φ ↦ k (Φ.length - 1)
    let cons : Deducer := dImpI L <| withCtx fun _ Φ₁ ↦
      let hA := Φ₁.length - 1
      withCtx fun _ Φ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ hA) .full) hA <|
      K.conjE <| withCtx fun _ Φ₂ ↦
      let (hH, hT) := (Φ₂.length - 2, Φ₂.length - 1)
      applyThm K "relQuoted" (fun Γ ↦ [hAt Γ, AAt Γ, RAt Γ]) [K.byHyp 0, K.byHyp hH] <|
      K.exE <| normLastK K <| withCtx fun Γ₃ _ ↦
      let tAt := atPos (Γ₃.length - 1)
      dAllE L K.G K.E 1 (tAt Γ₃) <|
      K.impE (linkK K "restQuotes: the head's relation" (K.byHyp hH)) <|
      lastIdx fun hOk ↦
      dImpE L 2 (K.byHyp hT) <| K.exE <| K.conjE <| withCtx fun Γ₄ Φ₄ ↦
      let tsAt := atPos (Γ₄.length - 1)
      let (hE, hW) := (Φ₄.length - 2, Φ₄.length - 1)
      let okAt (Γ : List Tree) : Term := pc P "Typing.fieldOk" [Term.snd (RAt Γ), rtyAt Γ,
        pc P "Typing.memberships" [Term.snd (RAt Γ), tAt Γ]]
      withCtx fun Γ Φ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ hE) .full) hE <|
      withCtx fun _ _ ↦
      dExI L K.G K.E (consT treeTy (tAt Γ) (tsAt Γ)) <| dConjI L
        (linkK K "restQuotes: the quotations" K.byNorm)
        (linkK K "restQuotes: the walk" (decideIn K okAt (K.hypFalse hOk) (K.byHyp hW)))
    let d₁ ← linkK K "restQuotes: construction" cons (Ls :: treeTy :: Γ₀.tail)
      (lowered.map Internal.weaken2 ++ [Internal.weakenElem φ]) (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ₀, hyps, φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The writer's end of the list of a constructor without a variable field denotes the empty list
value, of which the walk at the empty list holds. In the context of the last field's type and the
context. -/
def baseNil (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("baseNil", fun ix E ↦ do
    let K := ctorKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let vars := [treeTy, list treeTy]
    let at_ := denAt vars
    let (cx, rty) := (at_ 6, at_ 7)
    let z := pc P "Datatype.sx2" [pc P "Datatype.aNil" [], pc P "Datatype.aT" []]
    let plainOf (a : Term) : Term := notTest o (pc P "Prelude.isSome"
      [pc P "Reader.lookupAbbrev" [atomNameT a, at_ 1]])
    let hyps := [plainOf (pc P "Recognize.rNil" []), plainOf (pc P "Recognize.rT" [])]
    let thm : Internal.Thm := ⟨0, denCtx vars, hyps,
      listEndT P S (at_ 0) (at_ 1) (at_ 2) (at_ 3) cx (at_ 5) (Term.snd (at_ 0)) (leafT bnilT) rty
        (nilT treeTy) (pc P "Datatype.eraseExpr" [z])⟩
    let (cxAt) := atPos 6
    let scopeAt (Γ : List Tree) : Term := scopeOf P (atPos 1 Γ) (cxAt Γ)
    let fixedAt (Γ : List Tree) : List Term :=
      [atPos 5 Γ, scopeAt Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
    let nilForm : Term := pc P "Recognize.s2" [pc P "Recognize.rNil" [], pc P "Recognize.rT" []]
    let nilV : Term := treeList P (nilT treeTy)
    let main : Deducer :=
      applyThm K "denNil" fixedAt [K.byHyp 0, K.byHyp 1] <|
      K.cutThm "eraseAtom" (fun _ ↦ [call D.children [] [pc P "Datatype.aT" []]]) <|
      normLastK K <|
      withCtx fun _ _ ↦ dExI L K.G K.E (nilT treeTy) <| dExI L K.G K.E nilV <| dConjI L
        (linkK K "baseNil: the form" (applyThm K "denCong" (fun Γ ↦ [nilV, nilForm,
            pc P "Datatype.eraseExpr" [z]] ++ fixedAt Γ) [K.byNorm, dHyp] dHyp))
        (linkK K "baseNil: the walk" (K.solve 6))
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "baseNil: not proved" fun _ ↦ none
    pure (thm, d))

/-- The writer's end of the list of a constructor with a variable field, coerced to its annotation,
typed at the list of trees, denotes a list value of quotations of trees of which the walk holds: the
typing's parts ({name}`ofTyped`, {name}`atomTyped`), the annotation a type of lists
({name}`eraseTyList`), the value related there ({name}`restVarRel`, {name}`relListOf`), its elements
quotations ({name}`restQuotes`). In the context of the annotation, the marker's type of the field,
the context and the typing environment. -/
def baseVar (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("baseVar", fun ix E ↦ do
    let K := ctorKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let imp := Internal.Logic.imp o
    let childT ← primT Kernel.Prim.child
    let vars := [treeTy, treeTy, list treeTy, T.envTy]
    let at_ := denAt vars
    let (Ev, cx, rty, F) := (at_ 6, at_ 7, at_ 8, at_ 9)
    let aRest := pc P "Datatype.aRest" []
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let z := pc P "Typing.tOf" [F, aRest]
    let first (t : Term) : Term := apps childT [t, leafT bnilT]
    let readOf (Ev F : Term) : Term := getT (pc P "Typing.readTy" [Ev, rawT T Ev F])
    let synOf (Ev cx t : Term) : Term := pc P "Typing.synIn" [Ev, cx, t]
    let hyps : List Term := [T.numsT Ev (at_ 1), T.envT (at_ 0) cx (at_ 5),
        notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT aRest, at_ 1]])] ++
      atomFreeT P Ev aRest ++
      [Internal.Logic.all o treeTy (Term.lam treeTy (imp
        (Term.app (T.relT (sh 1 (at_ 0)) (first (readOf (sh 1 Ev) (sh 1 F)))) (quoteV P (v 0)))
        (truth o (pc P "Typing.fieldOk" [Term.snd (sh 1 (at_ 0)), sh 1 rty,
          pc P "Typing.memberships" [Term.snd (sh 1 (at_ 0)), v 0]]))))]
    let hCoh := hyps.length - 1
    let thm : Internal.Thm := ⟨0, denCtx vars, hyps, imp (isSomeT (synOf Ev cx z))
      (imp (Term.eq (getT (synOf Ev cx z)) (listOfTrees P))
        (listEndT P S (at_ 0) (at_ 1) (at_ 2) (at_ 3) cx (at_ 5) (Term.snd (at_ 0))
          (leafT (numeral 1)) rty (nilT treeTy) (pc P "Datatype.eraseExpr" [z])))⟩
    let (EAt, cxAt, rtyAt, FAt) := (atPos 6, atPos 7, atPos 8, atPos 9)
    let scopeAt (Γ : List Tree) : Term := scopeOf P (atPos 1 Γ) (cxAt Γ)
    let fixedAt (Γ : List Tree) : List Term :=
      [atPos 5 Γ, scopeAt Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
    let readAt (Γ : List Tree) : Term := readOf (EAt Γ) (FAt Γ)
    let synX (Γ : List Tree) : Term := getT (synOf (EAt Γ) (cxAt Γ) aRest)
    let normH (h : ℕ) (k : Deducer) : Deducer := withCtx fun _ Φ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h k
    let lastIdx (k : ℕ → Deducer) : Deducer := withCtx fun _ Φ ↦ k (Φ.length - 1)
    let notNum : Deducer := fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ [.delta (P.idx "Reader.numeral")]) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let charsOf : Term := call D.children [] [aRest]
    let main : Deducer := dImpI L <| dImpI L <| withCtx fun _ Φ₀ ↦
      let (hS, hE) := (Φ₀.length - 2, Φ₀.length - 1)
      applyThm K "ofTyped" (fun Γ ↦ [aRest, FAt Γ, cxAt Γ, EAt Γ]) [K.byHyp hS] <|
      K.conjE <| K.conjE <| K.conjE <| withCtx fun _ Φ₁ ↦
      let n := Φ₁.length
      let (hXs, hSame, hOf) := (n - 4, n - 2, n - 1)
      applyThm K "atomTyped" (fun Γ ↦ [charsOf, cxAt Γ, EAt Γ] ++ fixedAt Γ)
        [K.byHyp 0, K.byHyp 2, K.byHyp 3, K.byHyp 4, K.byHyp 5,
          linkK K "baseVar: not a numeral" notNum, K.byHyp hXs] <|
      K.conjE <| K.conjE <| withCtx fun _ Φ₂ ↦
      let m := Φ₂.length
      let (hNB, hLk, hTy) := (m - 4, m - 2, m - 1)
      applyThm K "restVarRel" (fun Γ ↦ [cxAt Γ, EAt Γ] ++ fixedAt Γ)
        [K.byHyp 0, K.byHyp 1, K.byHyp 2, K.byHyp hNB, K.byHyp hLk] <|
      K.exE <| K.conjE <| withCtx fun Γ₃ Φ₃ ↦
      let wAt := atPos (Γ₃.length - 1)
      let rW := Φ₃.length - 1
      K.cutThm "equalSound" (fun Γ ↦ [readAt Γ]) <| K.allEΓ synX <| K.impE (K.byHyp hSame) <|
      lastIdx fun e₁ ↦ normH hTy <| normH e₁ <| normH hOf <| normH hE <|
      applyThm K "eraseTyList" (fun Γ ↦ [readAt Γ]) [linkK K "baseVar: the erasure" (K.solve 3)] <|
      K.conjE <| withCtx fun _ Φ₄ ↦
      let (hLab, hFirst) := (Φ₄.length - 2, Φ₄.length - 1)
      normH hFirst <|
      applyThm K "relListOf" (fun Γ ↦ [wAt Γ, readAt Γ, atPos 0 Γ])
        [K.byHyp hLab, linkK K "baseVar: the relation" (K.byHyp rW)] <|
      K.conjE <| withCtx fun _ Φ₅ ↦
      let (hL, hAll) := (Φ₅.length - 2, Φ₅.length - 1)
      let vsAt (Γ : List Tree) : Term := call D.children []
        [getT (pc P "Eval.listOf" [wAt Γ])]
      applyThm K "restQuotes" (fun Γ ↦ [vsAt Γ, first (readAt Γ), rtyAt Γ, atPos 0 Γ])
        [linkK K "baseVar: the elements' erasure" (K.solve 3),
          linkK K "baseVar: the coherence" (K.byHyp hCoh)] <|
      K.impE (K.byHyp hAll) <| K.exE <| K.conjE <| withCtx fun Γ₆ Φ₆ ↦
      let tsAt := atPos (Γ₆.length - 1)
      let (hEl, hW) := (Φ₆.length - 2, Φ₆.length - 1)
      K.cutThm "eraseAtom" (fun _ ↦ [charsOf]) <| normLastK K <| normH hEl <|
      withCtx fun Γ _ ↦ dExI L K.G K.E (tsAt Γ) <| dExI L K.G K.E (wAt Γ) <| dConjI L
        (linkK K "baseVar: the atom" (applyThm K "denCong" (fun Γ ↦ [wAt Γ, aRest,
            pc P "Datatype.eraseExpr" [pc P "Typing.tOf" [FAt Γ, aRest]]] ++ fixedAt Γ)
          [linkK K "baseVar: the erasure's form" K.byNorm, dHyp] dHyp))
        (dConjI L (K.byHyp hL) (dConjI L (linkK K "baseVar: the trees" K.byNorm)
          (linkK K "baseVar: the walk" (K.byHyp hW))))
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "baseVar: not proved" fun _ ↦ none
    pure (thm, d))

/-- The writer's node of a position over a list. -/
def nodeOfForm (P : Prog) (n l : Term) : Term := listNode [pc P "Datatype.aNode" [], n, l]

/-- The kit of the application of the node primitive. -/
def nodeKit (P : Prog) (S : Defs) (T : Defs3) (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
  let K₀ := ctorKit P S T ix E
  let further := ["applyTyCons", "appsCons", "rawAtom", "rawList", "rawAtomR"].filter
    fun nm ↦ 0 < ix nm ∧ ix nm < E.size
  { K₀ with more := K₀.more ++ further }

/-- The typing at the application of the node primitive as its fold's step gives it. In the context
of the list, the position, the context and the typing environment. -/
def nodeSynEq (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("nodeSynEq", fun ix E ↦ do
    let K := nodeKit P S T ix E
    let P := K.P
    let Γ := [treeTy, treeTy, list treeTy, T.envTy]
    let t := pc P "Typing.synIn" [v 3, v 2, nodeOfForm P (v 1) (v 0)]
    let unfold : List Internal.NormRule := [.delta (T.argIdx 1), .delta (P.idx "Typing.synList")]
    let l ← nfE K.G K.E (K.rules []) Γ t
    let (r, d) ← lazyNf K.G K.E (K.rules [] ++ unfold) Γ 64 [] l
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The type of the primitive node: where its name is in neither the context nor the definitions
nor the numeral names. In the context of the context and the typing environment. -/
def nodeAtomTy (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("nodeAtomTy", fun ix E ↦ do
    let K₀ := nodeKit P S T ix E
    let unfolded := K₀.P.folded.filter (· != "Typing.synAtom")
    let K : Kit := { K₀ with
      P := { K₀.P with folded := unfolded }
      more := K₀.more ++ lookupEqNames.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size }
    let P := K.P
    let L := K.L
    let o := P.o
    let Γ := [list treeTy, T.envTy]
    let (cx, Ev) := (v 0, v 1)
    let aNode := pc P "Datatype.aNode" []
    let nameN := atomNameT aNode
    let thm : Internal.Thm := ⟨0, Γ,
      [notTest o (pc P "Prelude.isSome" [pc P "Typing.lookupName" [nameN, cx]]),
        notTest o (pc P "Prelude.isSome" [pc P "Typing.lookupName"
          [nameN, pc P "Typing.envDefs" [Ev]]]),
        notTest o (pc P "Typing.hasName" [nameN, pc P "Typing.envNums" [Ev]])],
      Term.eq (pc P "Typing.synAtom" [Ev, call D.children [] [aNode], cx])
        (pc P "Prelude.some" [pc P "Typing.tyArrow" [pc P "Typing.tyT" [],
          pc P "Typing.tyArrow" [listOfTrees P, pc P "Typing.tyT" []]]])⟩
    let (cxAt, EAt) := (atPos 1, atPos 0)
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let refuted (h : ℕ) : Deducer := dImpE L h (K.solve 3) lastFalse
    let lookupIn (xs : List Tree → Term) (Γ : List Tree) : Term :=
      pc P "Prelude.isSome" [pc P "Typing.lookupName" [nameN, xs Γ]]
    let main : Deducer :=
      decideIn K (fun Γ ↦ pc P "Typing.hasName" [nameN, pc P "Typing.envNums" [EAt Γ]])
        (decideIn K (lookupIn cxAt) (decideIn K (lookupIn (fun Γ ↦ pc P "Typing.envDefs" [EAt Γ]))
          (linkK K "nodeAtomTy: the primitive" fun Γ Φ ψ ↦
            dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0
              (K.rules Φ ++ [.delta (P.idx "Reader.numeral")]) Γ (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ)
          (refuted 1)) (refuted 0)) (refuted 2)
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "nodeAtomTy: not proved" fun _ ↦ none
    pure (thm, d))

/-- The application of the node primitive, typed, has as its second argument a list of trees: the
primitive's type, each argument's type decided. In the context of the list, the position, the
context and the typing environment. -/
def nodeTyped (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("nodeTyped", fun ix E ↦ do
    let K₀ := nodeKit P S T ix E
    let K : Kit := { K₀ with more := K₀.more ++ ["nodeSynEq"] }
    let P := K.P
    let o := P.o
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let Γ := [treeTy, treeTy, list treeTy, T.envTy]
    let (l, n, cx, Ev) := (v 0, v 1, v 2, v 3)
    let syn (t : Term) : Term := pc P "Typing.synIn" [Ev, cx, t]
    let aNode := pc P "Datatype.aNode" []
    let nameN := atomNameT aNode
    let thm : Internal.Thm := ⟨0, Γ,
      [notTest o (pc P "Prelude.isSome" [pc P "Typing.lookupName" [nameN, cx]]),
        notTest o (pc P "Prelude.isSome" [pc P "Typing.lookupName"
          [nameN, pc P "Typing.envDefs" [Ev]]]),
        notTest o (pc P "Typing.hasName" [nameN, pc P "Typing.envNums" [Ev]]),
        isSomeT (syn (nodeOfForm P n l))],
      Internal.Logic.conj o (isSomeT (syn l)) (Term.eq (getT (syn l)) (listOfTrees P))⟩
    let (lAt, nAt, cxAt, EAt) := (atPos 3, atPos 2, atPos 1, atPos 0)
    let synAt (t : List Tree → Term) (Γ : List Tree) : Term :=
      pc P "Typing.synIn" [EAt Γ, cxAt Γ, t Γ]
    let main : Deducer :=
      applyThm K "nodeAtomTy" (fun Γ ↦ [cxAt Γ, EAt Γ]) [K.byHyp 0, K.byHyp 1, K.byHyp 2] <|
      normLastK K <|
      decideOpt K (synAt nAt) (linkK K "nodeTyped: no position" (K.hypFalse 3)) <|
      decideIn K (fun Γ ↦ pc P "Typing.sameTy" [pc P "Typing.tyT" [], getT (synAt nAt Γ)])
        (linkK K "nodeTyped: the position not a tree" (K.hypFalse 3)) <|
      decideOpt K (synAt lAt) (linkK K "nodeTyped: no list" (K.hypFalse 3)) <|
      decideIn K (fun Γ ↦ pc P "Typing.sameTy" [listOfTrees P, getT (synAt lAt Γ)])
        (linkK K "nodeTyped: the list not of trees" (K.hypFalse 3)) <|
      K.cutThm "equalSymm" (fun Γ ↦ [getT (synAt lAt Γ), listOfTrees P]) <|
      K.impE (linkK K "nodeTyped: the test" (K.solve 3)) <|
      withCtx fun _ Φ₀ ↦
      let hSym := Φ₀.length - 1
      K.cutThm "equalSound" (fun Γ ↦ [getT (synAt lAt Γ)]) <|
      K.allEΓ (fun _ ↦ listOfTrees P) <|
      K.impE (K.byHyp hSym) <|
      normLastK K <| linkK K "nodeTyped: the list" (K.solve 4)
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "nodeTyped: not proved" fun _ ↦ none
    pure (thm, d))

/-- A coercion of a value to a datatype has a type: the value has a type, the erasure of that the
annotation reads, which the coercion's is. In the context of the value, the annotation, the context
and the typing environment. -/
def asTyped (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("asTyped", fun ix E ↦ do
    let K := ctorKit P S T ix E
    let P := K.P
    let o := P.o
    let conj := Internal.Logic.conj o
    let Γ := [treeTy, treeTy, list treeTy, T.envTy]
    let (x, f, cx, Ev) := (v 0, v 1, v 2, v 3)
    let syn (t : Term) : Term := pc P "Typing.synIn" [Ev, cx, t]
    let as' := pc P "Typing.tAs" [f, x]
    let read := pc P "Typing.readTy" [Ev, rawT T Ev f]
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let thm : Internal.Thm := ⟨0, Γ, [isSomeT (syn as')], conj (isSomeT (syn x))
      (Term.eq (getT (syn as')) (getT read))⟩
    let (xAt, fAt, cxAt, EAt) := (atPos 3, atPos 2, atPos 1, atPos 0)
    let synAt (t : List Tree → Term) (Γ : List Tree) : Term :=
      pc P "Typing.synIn" [EAt Γ, cxAt Γ, t Γ]
    let readAt (Γ : List Tree) : Term := pc P "Typing.readTy" [EAt Γ, rawT T (EAt Γ) (fAt Γ)]
    let main : Deducer :=
      decideOpt K readAt (linkK K "asTyped: no annotation" (K.hypFalse 0)) <|
      decideOpt K (synAt xAt) (linkK K "asTyped: no type" (K.hypFalse 0)) <|
      decideIn K (fun Γ ↦ pc P "Typing.sameTy" [pc P "Typing.eraseTy" [getT (readAt Γ)],
          getT (synAt xAt Γ)])
        (linkK K "asTyped: unequal" (K.hypFalse 0)) <|
      linkK K "asTyped: the parts" (K.solve 4)
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "asTyped: not proved" fun _ ↦ none
    pure (thm, d))

/-- The statement of the node of a constructor's position over the fields' values, coerced to the
datatype: where the list's end holds of the fields, the annotation reads the datatype and the
marker has the constructor, the form denotes a value related at its type. -/
def bodyThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  let o := P.o
  let imp := Internal.Logic.imp o
  let Ls := list treeTy
  let vars := [treeTy, treeTy, Ls, treeTy, treeTy, Ls, Ls, T.envTy]
  let at_ := denAt vars
  let (Ev, cx, cs, j, l, fts, flag, rty) :=
    (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11, at_ 12, at_ 13)
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let getT (t : Term) : Term := pc P "Prelude.get" [t]
  let syn (t : Term) : Term := pc P "Typing.synIn" [Ev, cx, t]
  let ms := Term.snd (at_ 0)
  let Da := nodeT (Term.pair (numeral 1) cs)
  let nameD := atomNameT Da
  let form := pc P "Typing.tAs" [Da, nodeOfForm P (pc P "Recognize.num" [j]) l]
  let aNode := pc P "Datatype.aNode" []
  let nameN := atomNameT aNode
  let rNode := pc P "Recognize.rNode" []
  let Lss := list Ls
  let lastAll : Term := Internal.Logic.all o Lss (Term.lam Lss (imp
    (truth o (walkT P (Term.snd (sh 1 (at_ 0))) (sh 1 flag) (sh 1 rty) (sh 1 fts) (v 0)))
    (truth o (anyT P (pc P "Typing.ctorOk" [Term.snd (sh 3 (at_ 0)), v 1,
        leafT (call D.lab [] [sh 3 j]), v 2])
      (specsOf P (Term.snd (sh 1 (at_ 0))) (sh 1 Da))))))
  let hyps : List Term :=
    [notTest o (pc P "Prelude.isSome" [pc P "Typing.lookupName" [nameN, cx]]),
      notTest o (pc P "Prelude.isSome" [pc P "Typing.lookupName"
        [nameN, pc P "Typing.envDefs" [Ev]]]),
      notTest o (pc P "Typing.hasName" [nameN, pc P "Typing.envNums" [Ev]]),
      numT P (at_ 1)] ++
    ((absentTests P rNode (scopeOf P (at_ 1) cx) (at_ 2)).map (notTest o)) ++
    [notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT rNode, at_ 1]]),
      imp (isSomeT (syn l)) (imp (Term.eq (getT (syn l)) (listOfTrees P))
        (listEndT P S (at_ 0) (at_ 1) (at_ 2) (at_ 3) cx (at_ 5) ms flag rty fts
          (pc P "Datatype.eraseExpr" [l]))),
      Term.eq (getT (pc P "Typing.readTy" [Ev, rawT T Ev Da])) (pc P "Typing.tyData" [nameD]),
      lastAll]
  ⟨0, denCtx vars, hyps, imp (isSomeT (syn form))
    (Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
      (denT P S (sh 1 (at_ 0)) (sh 1 (at_ 3)) (sh 1 (at_ 2)) (sh 1 (at_ 1))
        (sh 1 (scopeOf P (at_ 1) cx)) (sh 1 (at_ 5)) (sh 1 (pc P "Datatype.eraseExpr" [form]))
        (v 0))
      (Term.app (T.relT (sh 1 (at_ 0)) (getT (sh 1 (syn form)))) (v 0)))))⟩

/-- The erasure at the application of the node primitive to an atom: the application of the
erasures. In the context of the list and the atom's characters. -/
def nodeEraseEq (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("nodeEraseEq", fun ix E ↦ do
    let K := nodeKit P S T ix E
    let P := K.P
    let Γ := [treeTy, list treeTy]
    let t := pc P "Datatype.eraseExpr" [nodeOfForm P (nodeT (Term.pair (numeral 1) (v 1))) (v 0)]
    let unfold := (List.range nFolds).map fun k ↦ Internal.NormRule.delta (T.argIdx k)
    let l ← nfE K.G K.E (K.rules []) Γ t
    let (r, d) ← lazyNf K.G K.E (K.rules [] ++ unfold) Γ 64 [] l
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The quotation of a member of a datatype is related at the datatype: the relation unfolded at the
datatype, its witness the member. In the context of the member, the datatype's name and the
relation's context. -/
def relDataIntro (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relDataIntro", fun ix E ↦ do
    let K₀ := ctorKit P S T ix E
    let rebuilding := relRebuildNames.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size
    let K : Kit := { K₀ with more := K₀.more ++ rebuilding }
    let P := K.P
    let L := K.L
    let (t, n, R) := (v 0, v 1, v 2)
    let thm : Internal.Thm := ⟨0, [treeTy, treeTy, Defs3.ctxTy],
      [truth P.o (pc P "Typing.memberOf" [Term.snd R,
        nodeT (Term.pair (numeral 1) (call D.children [] [n])), t])],
      Term.app (T.relT R (pc P "Typing.tyData" [n])) (quoteV P t)⟩
    let some d := (fun Γ Φ ψ ↦
        dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta T.q]) .full) (fun Γ Φ ψ ↦
          dExI L K.G K.E (v 0) (K.norm (dConjI L (K.solve 3)
            (linkK K "relDataIntro: the member" (K.byHyp 0)))) Γ Φ ψ) Γ Φ ψ)
        thm.ctx thm.hyps thm.concl
      | dbgTrace "relDataIntro: not proved" fun _ ↦ none
    pure (thm, d))

/-- The node of a constructor's position over the fields' values, coerced to the datatype
({name}`bodyThm`): the typing's parts ({name}`asTyped`, {name}`nodeTyped`), the list's end, the
node's denotation ({name}`denNodeL`) and its membership by the marker's constructor
({name}`ctorsMember`), the relation unfolded at the datatype. -/
def bodyRel (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("bodyRel", fun ix E ↦ do
    let K₀ := nodeKit P S T ix E
    let rebuilding := relRebuildNames.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size
    let K : Kit := { K₀ with more := K₀.more ++ ["nodeEraseEq"] ++ rebuilding }
    let P := K.P
    let L := K.L
    let thm := bodyThm P S T
    let nH := thm.hyps.length
    let (EAt, cxAt, csAt, jAt, lAt) := (atPos 6, atPos 7, atPos 8, atPos 9, atPos 10)
    let scopeAt (Γ : List Tree) : Term := scopeOf P (atPos 1 Γ) (cxAt Γ)
    let fixedAt (Γ : List Tree) : List Term :=
      [atPos 5 Γ, scopeAt Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
    let msAt (Γ : List Tree) : Term := Term.snd (atPos 0 Γ)
    let DaAt (Γ : List Tree) : Term := nodeT (Term.pair (numeral 1) (csAt Γ))
    let numAt (Γ : List Tree) : Term := pc P "Recognize.num" [jAt Γ]
    let bAt (Γ : List Tree) : Term := nodeOfForm P (numAt Γ) (lAt Γ)
    let formAt (Γ : List Tree) : Term := pc P "Typing.tAs" [DaAt Γ, bAt Γ]
    let lFAt (Γ : List Tree) : Term := pc P "Datatype.eraseExpr" [lAt Γ]
    let (hNum, hAb1, hAb2, hPlain, hEnd, hRead, hMark) :=
      (3, 4, 5, 6, 7, 8, 9)
    let normH (h : ℕ) (k : Deducer) : Deducer := withCtx fun _ Φ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h k
    let main : Deducer := dImpI L <|
      applyThm K "asTyped" (fun Γ ↦ [bAt Γ, DaAt Γ, cxAt Γ, EAt Γ]) [K.byHyp nH] <|
      K.conjE <| withCtx fun _ Φ₁ ↦
      let (hB, hA) := (Φ₁.length - 2, Φ₁.length - 1)
      normH hRead <| normH hA <|
      applyThm K "nodeTyped" (fun Γ ↦ [lAt Γ, numAt Γ, cxAt Γ, EAt Γ])
        [K.byHyp 0, K.byHyp 1, K.byHyp 2, K.byHyp hB] <|
      K.conjE <| withCtx fun _ Φ₂ ↦
      let (hLs₀, hLe) := (Φ₂.length - 2, Φ₂.length - 1)
      normH hLe <| dImpE L hEnd (K.byHyp hLs₀) <|
      K.impE (linkK K "bodyRel: the list's type" K.byNorm) <|
      K.exE <| K.exE <| K.conjE <| K.conjE <| K.conjE <| withCtx fun Γ₃ Φ₃ ↦
      let (tsAt, wAt) := (atPos (Γ₃.length - 2), atPos (Γ₃.length - 1))
      let n₃ := Φ₃.length
      let (hLs, hEq, hWalk) := (n₃ - 4, n₃ - 2, n₃ - 1)
      normH hEq <|
      withCtx fun Γ _ ↦ dAllE L K.G K.E hNum (jAt Γ) <| normLastK K <|
      K.conjE <| withCtx fun _ Φ₄ ↦
      let hp := Φ₄.length - 2
      K.conjE <| withCtx fun _ Φ₅ ↦
      applyThm K "denNum" (fun Γ ↦ jAt Γ :: fixedAt Γ) [K.byHyp hp, K.byNorm,
        K.byHyp (Φ₅.length - 1)] <|
      applyThm K "denNodeL" (fun Γ ↦ [tsAt Γ, wAt Γ, jAt Γ, lFAt Γ, numAt Γ] ++ fixedAt Γ)
        [K.byHyp hAb1, K.byHyp hAb2, K.byHyp hPlain, K.byHyp hLs,
          linkK K "bodyRel: the trees" K.byNorm, dHyp, dHyp] <|
      withCtx fun Γ₆ _ ↦
      dAllE L K.G K.E hMark (membershipsT P (msAt Γ₆) (tsAt Γ₆)) <| K.impE (K.byHyp hWalk) <|
      withCtx fun _ Φ₇ ↦
      let tAt (Γ : List Tree) : Term := nodeT (Term.pair (call D.lab [] [jAt Γ]) (tsAt Γ))
      applyThm K "ctorsMember" (fun Γ ↦ [tAt Γ, DaAt Γ, msAt Γ])
        [linkK K "bodyRel: the constructor" (K.byHyp (Φ₇.length - 1))] <|
      withCtx fun _ Φ₈ ↦
      let hM := Φ₈.length - 1
      let nodeF (Γ : List Tree) : Term := pc P "Recognize.s3" [pc P "Recognize.rNode" [], numAt Γ,
        lFAt Γ]
      withCtx fun Γ _ ↦ dExI L K.G K.E (quoteV P (tAt Γ)) <| dConjI L
        (linkK K "bodyRel: the node's form" (applyThm K "denCong" (fun Γ ↦ [quoteV P (tAt Γ),
            nodeF Γ, pc P "Datatype.eraseExpr" [formAt Γ]] ++ fixedAt Γ)
          [linkK K "bodyRel: the erasure" K.byNorm, dHyp] dHyp))
        (linkK K "bodyRel: the relation" <|
          applyThm K "relDataIntro" (fun Γ ↦ [tAt Γ, atomNameT (DaAt Γ), atPos 0 Γ]) [K.byHyp hM] <|
          fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "bodyRel: not proved" fun _ ↦ none
    pure (thm, d))

/-- The kit of an abstraction over one binder of the constructors. -/
def lamKit (P : Prog) (S : Defs) (T : Defs3) (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
  let K₀ := nodeKit P S T ix E
  let W := kwKit P S T ix E 3 [false, false, true] "Reader.kwLam" true
  { K₀ with more := (K₀.more ++ W.K.more ++ ["rawListR"].filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size).eraseDups }

/-- The stage functions' equations at an abstraction over one binder, under the folded program. -/
def lamEqs (P : Prog) (T : Defs3) : List Step :=
  let P' := { walkProg P with folded := (walkProg P).folded ++ ["Typing.decimalChars"] }
  rawListR P' T :: kwEqs P' T "Reader.kwLam" 3 (lamOneForm P) true

/-- The form of an abstraction over one binder, a name at an annotation, in a body. -/
def lamForm (P : Prog) (a F b : Term) : Term :=
  listNode [kwAtom P "Reader.kwLam", listNode [listNode [a, F]], b]

/-- An abstraction over one binder, typed: the annotation has a type and the body one in the context
extended by the binder at it, the abstraction's an arrow between them. In the context of the body,
the annotation, the binder's name, the context and the typing environment. -/
def lamTypedOne (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("lamTypedOne", fun ix E ↦ do
    let K := lamKit P S T ix E
    let P := K.P
    let o := P.o
    let conj := Internal.Logic.conj o
    let Γ := [treeTy, treeTy, treeTy, list treeTy, T.envTy]
    let (b, F, a, cx, Ev) := (v 0, v 1, v 2, v 3, v 4)
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let read := pc P "Typing.readTy" [Ev, rawT T Ev F]
    let entry := pc P "Typing.abbr" [pc P "Typing.atomName" [rawT T Ev a], getT read]
    let synB := pc P "Typing.synIn" [Ev, consT treeTy entry cx, b]
    let whole := pc P "Typing.synIn" [Ev, cx, lamForm P a F b]
    let thm : Internal.Thm := ⟨0, Γ, [isSomeT whole], conj (isSomeT read) (conj (isSomeT synB)
      (Term.eq (getT whole) (pc P "Typing.tyArrow" [getT read, getT synB])))⟩
    let (bAt, FAt, aAt, cxAt, EAt) := (atPos 4, atPos 3, atPos 2, atPos 1, atPos 0)
    let readAt (Γ : List Tree) : Term := pc P "Typing.readTy" [EAt Γ, rawT T (EAt Γ) (FAt Γ)]
    let entryAt (Γ : List Tree) : Term := pc P "Typing.abbr"
      [pc P "Typing.atomName" [rawT T (EAt Γ) (aAt Γ)], getT (readAt Γ)]
    let bodyAt (Γ : List Tree) : Term := pc P "Typing.synIn"
      [EAt Γ, consT treeTy (entryAt Γ) (cxAt Γ), bAt Γ]
    let main : Deducer :=
      decideIn K (fun Γ ↦ pc P "Typing.binderName" [EAt Γ, rawT T (EAt Γ) (aAt Γ)])
        (linkK K "lamTypedOne: not a binder" (K.hypFalse 0)) <|
      decideOpt K readAt (linkK K "lamTypedOne: no annotation" (K.hypFalse 0)) <|
      decideOpt K bodyAt (linkK K "lamTypedOne: no body" (K.hypFalse 0)) <|
      linkK K "lamTypedOne: the parts" (K.solve 5)
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "lamTypedOne: not proved" fun _ ↦ none
    pure (thm, d))

/-- The development of the constructors' bodies. -/
def constructorBodyDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [eraseTyList P S T, relListOf P S T, restQuotes P S T, baseNil P S T, baseVar P S T,
    nodeSynEq P S T, nodeAtomTy P S T, nodeTyped P S T, asTyped P S T, nodeEraseEq P S T,
    relDataIntro P S T, bodyRel P S T] ++ lamEqs P T ++ [lamTypedOne P S T]

/-- The development of {name}`constructorBodyDev`, after that of {name}`constructorDev`, stored as
the certificate {lit}`datatype-constructor-body`. -/
def constructorBodyCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := walkAfter P S T | throw "the base is not stated"
  certifyAfter P (names ++ (walkDev P S T).map (·.1) ++ (recognizerDev P S T).map (·.1) ++
    (recognizerFoldDev P S T).map (·.1) ++ (constructorDev P S T).map (·.1))
    "datatype-constructor-body" (constructorBodyDev P S T) before

/-- The tests of an atom's being named by a keyword of the typing's erasure. -/
def binderKws : List String := ["Typing.kwRep", "Typing.kwDecode", "Typing.kwDatum"]

/-- The erasure of an abstraction over one binder, an atom named by no keyword of the erasure: the
abstraction of the erasure of the annotation over that of the body. In the context of the body, the
annotation and the atom's characters. -/
def eraseLam (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("eraseLam", fun ix E ↦ do
    let K := lamKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let Γ := [treeTy, treeTy, list treeTy]
    let (b, F, cs) := (v 0, v 1, v 2)
    let a := nodeT (Term.pair (numeral 1) cs)
    let er (t : Term) : Term := pc P "Datatype.eraseExpr" [t]
    let named (kw : String) : Term := notTest o (pc P "Typing.namedTx" [a, pc P kw []])
    let thm : Internal.Thm := ⟨0, Γ, binderKws.map named,
      Term.eq (er (lamForm P a F b)) (pc P "Recognize.s3" [pc P "Recognize.rLam" [],
        listNode [listNode [a, er F]], er b])⟩
    let aAt (Γ : List Tree) : Term := nodeT (Term.pair (numeral 1) (atPos 0 Γ))
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let decided : Deducer := binderKws.zipIdx.foldr (fun (kw, i) k ↦
      decideIn K (fun Γ ↦ pc P "Typing.namedTx" [aAt Γ, pc P kw []]) k
        (dImpE L i (K.solve 3) lastFalse))
      (linkK K "eraseLam: the sides" K.byNorm)
    let some d := decided thm.ctx thm.hyps thm.concl
      | dbgTrace "eraseLam: not proved" fun _ ↦ none
    pure (thm, d))

/-- The writer's abstraction over one binder denotes the closure of its environment over the body's
resolved term, where the binder reads as a name at a type and the body resolves in the scope of the
name. -/
def denLamIs (P : Prog) : DenRule :=
  let Tt := treeTy
  let vars := [Tt, Tt, Tt, Tt]
  let at_ := denAt vars
  let (b, e, A, x) := (at_ 6, at_ 7, at_ 8, at_ 9)
  let rLam := pc P "Recognize.rLam" []
  let ps := consT treeTy (kNode 0 [x, A]) (nilT treeTy)
  let res := pc P "Reader.resolve" [at_ 3, at_ 2, pc P "Reader.expandNums" [at_ 1, e],
    consT treeTy x (at_ 4)]
  { name := "denLamIs", vars, plain := [rLam],
    more := [Term.eq (pc P "Reader.readBinders" [at_ 3, pc P "Reader.binders"
        [pc P "Reader.expandNums" [at_ 1, b]]]) (pc P "Prelude.some" [node0 ps]),
      truth P.o (pc P "Prelude.isSome" [res])],
    form := pc P "Recognize.s3" [rLam, b, e],
    value := pc P "Eval.valClo" [at_ 5, A, pc P "Prelude.get" [res]], levels := 1,
    pre := fun K up k ↦ decideIn K (up (pc P "Prelude.isSome" [res])) (K.hypFalse 2) k }

/-- The reader's binders of an abstraction over one binder, an atom named by no abbreviation, its
characters fixed by the expansion of the numeral abbreviations, at an annotation reading as a type:
the node of the name at the type. In the context of the type, the annotation, the characters, the
numeral abbreviations and the type abbreviations. -/
def readBinderOne (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("readBinderOne", fun ix E ↦ do
    let K := denKit P S ix E
    let P := K.P
    let Ls := list treeTy
    let Γ := [treeTy, treeTy, Ls, Ls, Ls]
    let (A, F, cs, nums, tys) := (v 0, v 1, v 2, v 3, v 4)
    let a := nodeT (Term.pair (numeral 1) cs)
    let fn := Term.lam treeTy (pc P "Reader.expandNums" [sh 1 nums, v 0])
    let thm : Internal.Thm := ⟨0, Γ,
      [notTest P.o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT a, nums]]),
        truth P.o (pc P "charsFixed" [fn, cs]),
        Term.eq (pc P "Reader.readType" [tys, pc P "Reader.expandNums" [nums, F]])
          (pc P "Prelude.some" [A])],
      Term.eq (pc P "Reader.readBinders" [tys, pc P "Reader.binders"
          [pc P "Reader.expandNums" [nums, listNode [listNode [a, F]]]]])
        (pc P "Prelude.some" [node0 (consT treeTy (kNode 0 [atomNameT a, A]) (nilT treeTy))])⟩
    let (csAt, numsAt) := (atPos 2, atPos 1)
    let unfold := resolveRules P T ix E ++ [.delta (T.argIdx 3)]
    let aAt (Γ : List Tree) : Term := nodeT (Term.pair (numeral 1) (csAt Γ))
    let main : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev"
          [atomNameT (aAt Γ), numsAt Γ]])
        (K.cutThm "charsFixedEq" (fun Γ ↦ [csAt Γ, numsAt Γ]) <| K.impE (K.byHyp 1) <|
          normLastK K <| withCtx fun _ Φ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ 2) .full) 2 <|
          linkK K "readBinderOne: the sides" fun Γ Φ ψ ↦
            dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold) Γ
              (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ)
        (dImpE K.L 0 (K.solve 3) fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "readBinderOne: not proved" fun _ ↦ none
    pure (thm, d))

/-- The body of an abstraction resolves where the abstraction does, its binder reading as a name at
a type. In the context of {name}`denCtx` of the body and the binders, the name and the type. -/
def lamRead (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("lamRead", fun ix E ↦ do
    let K := denKit P S ix E
    let P := K.P
    let vars := [treeTy, treeTy, treeTy, treeTy]
    let at_ := denAt vars
    let (b, e, A, x) := (at_ 6, at_ 7, at_ 8, at_ 9)
    let rLam := pc P "Recognize.rLam" []
    let ps := consT treeTy (kNode 0 [x, A]) (nilT treeTy)
    let resOf (t scope : Term) : Term := pc P "Reader.resolve" [at_ 3, at_ 2,
      pc P "Reader.expandNums" [at_ 1, t], scope]
    let thm : Internal.Thm := ⟨0, denCtx vars,
      [notTest P.o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT rLam, at_ 1]]),
        Term.eq (pc P "Reader.readBinders" [at_ 3, pc P "Reader.binders"
          [pc P "Reader.expandNums" [at_ 1, b]]]) (pc P "Prelude.some" [node0 ps]),
        truth P.o (pc P "Prelude.isSome" [resOf (pc P "Recognize.s3" [rLam, b, e]) (at_ 4)])],
      truth P.o (pc P "Prelude.isSome" [resOf e (consT treeTy x (at_ 4))])⟩
    let unfold := resolveRules P T ix E ++ [.delta (T.argIdx 3)]
    let eAt := atPos 7
    let bodyAt (Γ : List Tree) : Term := pc P "Reader.resolve" [atPos 3 Γ, atPos 2 Γ,
      pc P "Reader.expandNums" [atPos 1 Γ, eAt Γ], consT treeTy (atPos 9 Γ) (atPos 4 Γ)]
    let main : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev"
          [atomNameT rLam, atPos 1 Γ]])
        (withCtx fun _ Φ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ 1) .full) 1 <|
          decideOpt K bodyAt
            (linkK K "lamRead: no body" fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ 2 ++ unfold) .full) 2 (dFalse K.L dHyp) Γ Φ ψ)
            (linkK K "lamRead: the body" (K.solve 3)))
        (dImpE K.L 0 (K.solve 3) fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "lamRead: not proved" fun _ ↦ none
    pure (thm, d))

/-- The development of the abstractions of the constructors' fields. -/
def constructorLamDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [eraseLam P S T, denRule P S T (denLamIs P), readBinderOne P S T, lamRead P S T]

/-- The development of {name}`constructorLamDev`, after that of {name}`constructorBodyDev`, stored
as the certificate {lit}`datatype-constructor-lam`. -/
def constructorLamCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := walkAfter P S T | throw "the base is not stated"
  certifyAfter P (names ++ (walkDev P S T).map (·.1) ++ (recognizerDev P S T).map (·.1) ++
    (recognizerFoldDev P S T).map (·.1) ++ (constructorDev P S T).map (·.1) ++
    (constructorBodyDev P S T).map (·.1))
    "datatype-constructor-lam" (constructorLamDev P S T) before

/-- The soundness at a form of a constructor's definition, beneath the quantifiers over the context
and the environment: the context and the environment related, the name of the node primitive in
neither the context nor the scope, the form typed and resolved, it denotes a value related at its
type. -/
def formSoundT (P : Prog) (S : Defs) (T : Defs3) (R nums names tys Ev x cx env : Term) : Term :=
  let o := P.o
  let imp := Internal.Logic.imp o
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let aNode := pc P "Datatype.aNode" []
  let nameN := atomNameT aNode
  let scope := scopeOf P nums cx
  let er := pc P "Datatype.eraseExpr" [x]
  let syn := pc P "Typing.synIn" [Ev, cx, x]
  let res := pc P "Reader.resolve" [tys, names, pc P "Reader.expandNums" [nums, er], scope]
  imp (T.envT R cx env) <|
  imp (notTest o (pc P "Prelude.isSome" [pc P "Typing.lookupName" [nameN, cx]])) <|
  imp (notTest o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [nameN, scope]])) <|
  imp (isSomeT syn) <| imp (isSomeT res) <|
  Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
    (denT P S (sh 1 R) (sh 1 tys) (sh 1 names) (sh 1 nums) (sh 1 scope) (sh 1 env) (sh 1 er) (v 0))
    (Term.app (T.relT (sh 1 R) (pc P "Prelude.get" [sh 1 syn])) (v 0))))

/-- The soundness at a form at every context and environment. -/
def formAllT (P : Prog) (S : Defs) (T : Defs3) (R nums names tys Ev x : Term) : Term :=
  let o := P.o
  let Ls := list treeTy
  let u (t : Term) : Term := sh 2 t
  Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o Ls (Term.lam Ls
    (formSoundT P S T (u R) (u nums) (u names) (u tys) (u Ev) (u x) (v 1) (v 0)))))

/-- That a tree is a binder of a constructor's definition, in the context of the numeral and type
abbreviations: an atom at an annotation reading as a type, the atom named by no abbreviation, no
keyword of the erasure and not the node primitive, its characters fixed by the expansion of the
numeral abbreviations. Beneath the type v0, the annotation v1 and the characters v2. -/
def binderOkT (P : Prog) (nums tys b : Term) : Term :=
  let o := P.o
  let Ls := list treeTy
  let u (t : Term) : Term := sh 3 t
  let (A, F, cs) := (v 0, v 1, v 2)
  let a := nodeT (Term.pair (numeral 1) cs)
  let fn := Term.lam treeTy (pc P "Reader.expandNums" [sh 1 (u nums), v 0])
  let equalT := (primT Kernel.Prim.equal).getD Term.star
  let parts : List Term :=
    [Term.eq (u b) (listNode [a, F]),
      notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT a, u nums]]),
      truth o (pc P "charsFixed" [fn, cs])] ++
    binderKws.map (fun kw ↦ notTest o (pc P "Typing.namedTx" [a, pc P kw []])) ++
    [notTest o (apps equalT [atomNameT (pc P "Datatype.aNode" []), atomNameT a]),
      Term.eq (pc P "Reader.readType" [u tys, pc P "Reader.expandNums"
        [u nums, pc P "Datatype.eraseExpr" [F]]]) (pc P "Prelude.some" [A])]
  Internal.Logic.ex o Ls (Term.lam Ls (Internal.Logic.ex o treeTy (Term.lam treeTy
    (Internal.Logic.ex o treeTy (Term.lam treeTy
      (parts.dropLast.foldr (Internal.Logic.conj o) (parts.getLastD Term.star)))))))

/-- The soundness at the abstractions over a list of binders around a form, given that at the form:
by induction on the binders. A construction: the abstraction's typing ({name}`lamTypedOne`) and
erasure ({name}`eraseLam`), its reading ({name}`readBinderOne`, {name}`lamRead`) and denotation
({name}`denLamIs`), its closure related at the arrow ({lit}`relTArrow`): at a value related at the
annotation, the induction hypothesis at the context and the environment extended. -/
def ctorNest (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("ctorNest", fun ix E ↦ do
    let K₀ := lamKit P S T ix E
    let K : Kit := { K₀ with more := (K₀.more ++ ["relTArrow"] ++ lookupEqNames.filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size).eraseDups }
    let P := K.P
    let L := K.L
    let o := P.o
    let imp := Internal.Logic.imp o
    let Ls := list treeTy
    let Γ₀ := [Ls, treeTy, T.envTy, Ls, Ls, Ls, Defs3.ctxTy]
    let (bs, body, Ev, tys, names, nums, R) := (v 0, v 1, v 2, v 3, v 4, v 5, v 6)
    let rLam := pc P "Recognize.rLam" []
    let hyps : List Term := [T.numsT Ev nums,
      notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT rLam, nums]]),
      formAllT P S T R nums names tys Ev body]
    let oks (xs : Term) : Term := S.allL
      (Term.lam treeTy (binderOkT P (sh 1 nums) (sh 1 tys) (v 0))) xs
    let φ := imp (oks bs) (formAllT P S T R nums names tys Ev (nestT P bs body))
    let some lowered := Internal.lowerHyps P.G 0 Γ₀.tail hyps
      | dbgTrace "ctorNest: the hypotheses" fun _ ↦ none
    let d₀ ← (linkK K "ctorNest: no binders" <| dImpI L (K.byHyp 2)) Γ₀.tail lowered
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let ih := hyps.length
    let (RAt, numsAt, namesAt, tysAt, EAt, bodyAt, tlAt) :=
      (atPos 0, atPos 1, atPos 2, atPos 3, atPos 4, atPos 5, atPos 7)
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let aNode := pc P "Datatype.aNode" []
    let nameN := atomNameT aNode
    let equalT ← primT Kernel.Prim.equal
    let normH (h : ℕ) (k : Deducer) : Deducer := withCtx fun _ Φ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h k
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    -- the name of the node primitive other than the binder's, each way about; then k
    let unequalThen (nAt : List Tree → Term) (hNe : ℕ) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ apps equalT [nameN, nAt Γ])
        (decideIn K (fun Γ ↦ apps equalT [nAt Γ, nameN]) k
          (K.cutThm "equalSymm" (fun Γ ↦ [nameN, nAt Γ]) <| K.impE (K.solve 3) <|
            fun Γ Φ ψ ↦ dImpE L hNe (K.byHyp (Φ.length - 1)) lastFalse Γ Φ ψ))
        (dImpE L hNe (K.solve 3) lastFalse)
    let XAt (Γ : List Tree) : Term := nestT P (tlAt Γ) (bodyAt Γ)
    let cons : Deducer := dImpI L <| withCtx fun _ Φ₁ ↦
      let hC := Φ₁.length - 1
      normH hC <| K.conjE <| withCtx fun Γ₂ Φ₂ ↦
      let (hOk, hT) := (Φ₂.length - 2, Φ₂.length - 1)
      let p₀ := Γ₂.length
      let (csAt, FAt, AAt) := (atPos p₀, atPos (p₀ + 1), atPos (p₀ + 2))
      dExE L K.G K.E hOk <| K.exE <| K.exE <|
      K.conjE <| K.conjE <| K.conjE <| K.conjE <| K.conjE <| K.conjE <| K.conjE <|
      withCtx fun _ Φ₃ ↦
      let n₃ := Φ₃.length
      let (hB, hPl, hFx, hK₁, hK₂, hK₃, hNe, hRd) :=
        (n₃ - 14, n₃ - 12, n₃ - 10, n₃ - 8, n₃ - 6, n₃ - 4, n₃ - 2, n₃ - 1)
      normH hRd <|
      let aAt (Γ : List Tree) : Term := nodeT (Term.pair (numeral 1) (csAt Γ))
      let nAt (Γ : List Tree) : Term := atomNameT (aAt Γ)
      let binderF (Γ : List Tree) : Term := listNode [listNode [aAt Γ,
        pc P "Datatype.eraseExpr" [FAt Γ]]]
      let eX (Γ : List Tree) : Term := pc P "Datatype.eraseExpr" [XAt Γ]
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [nAt Γ, numsAt Γ]])
        (dAllI L <| dAllI L <| withCtx fun Γ₄ _ ↦
        let (cxAt, envAt) := (atPos (Γ₄.length - 2), atPos (Γ₄.length - 1))
        let scopeAt (Γ : List Tree) : Term := scopeOf P (numsAt Γ) (cxAt Γ)
        let fixedAt (Γ : List Tree) : List Term :=
          [envAt Γ, scopeAt Γ, tysAt Γ, namesAt Γ, numsAt Γ, RAt Γ]
        dImpI L <| dImpI L <| dImpI L <| dImpI L <| dImpI L <| withCtx fun _ Φ₅ ↦
        let n₅ := Φ₅.length
        let (hEnv, hN₁, hN₂, hS, hR) := (n₅ - 5, n₅ - 4, n₅ - 3, n₅ - 2, n₅ - 1)
        let bits := [D.bnil, D.b0, D.b1].map Internal.NormRule.delta
        let raw₁ : List Internal.NormRule := Translation.baseRules ++ bits ++ [.hyp hB]
        -- a hypothesis and the goal, rewritten by equations alone
        let rawHyp (rs : List Internal.NormRule) (h : ℕ) : Deducer :=
          dRwHyp (evalRw K.G K.E rs .full) h <|
            dRwBy (evalRw K.G K.E rs .full) dHyp
        applyThm K "lamTypedOne" (fun Γ ↦ [XAt Γ, FAt Γ, aAt Γ, cxAt Γ, EAt Γ])
          [rawHyp raw₁ hS] <|
        K.conjE <| K.conjE <| withCtx fun _ Φ₆ ↦
        let n₆ := Φ₆.length
        let hSynB := n₆ - 2
        dRwHyp (evalRw K.G K.E raw₁ .full) (n₆ - 1) <| withCtx fun _ Φ₆₂ ↦
        let hArr := Φ₆₂.length - 1
        let readAt (Γ : List Tree) : Term :=
          getT (pc P "Typing.readTy" [EAt Γ, rawT T (EAt Γ) (FAt Γ)])
        let entryAt (Γ : List Tree) : Term := pc P "Typing.abbr"
          [pc P "Typing.atomName" [rawT T (EAt Γ) (aAt Γ)], readAt Γ]
        applyThm K "eraseLam" (fun Γ ↦ [XAt Γ, FAt Γ, csAt Γ])
          [K.byHyp hK₁, K.byHyp hK₂, K.byHyp hK₃] <|
        withCtx fun _ Φₑ ↦
        dRwHyp (evalRw K.G K.E raw₁ .full) (Φₑ.length - 1) <| withCtx fun _ Φₑ₂ ↦
        let hEr := Φₑ₂.length - 1
        applyThm K "readBinderOne" (fun Γ ↦ [AAt Γ, pc P "Datatype.eraseExpr" [FAt Γ], csAt Γ,
            numsAt Γ, tysAt Γ])
          [K.byHyp hPl, K.byHyp hFx, linkK K "ctorNest: the annotation" K.byNorm] <|
        let raw₂ : List Internal.NormRule := raw₁ ++ [.hyp hEr]
        let σ (Γ : List Tree) : List Term :=
          [nAt Γ, AAt Γ, eX Γ, binderF Γ] ++ fixedAt Γ
        applyThm K "lamRead" σ [K.byHyp 1, dHyp, rawHyp raw₂ hR] <| withCtx fun _ Φ₇ ↦
        let hResB := Φ₇.length - 1
        applyThm K "denLamIs" σ [K.byHyp 1, dHyp, dHyp] <|
        withCtx fun Γ Φₗ ↦
        let hLam := Φₗ.length - 1
        let resB (Γ : List Tree) : Term := pc P "Reader.resolve" [tysAt Γ, namesAt Γ,
          pc P "Reader.expandNums" [numsAt Γ, eX Γ], consT treeTy (nAt Γ) (scopeAt Γ)]
        let cloAt (Γ : List Tree) : Term :=
          pc P "Eval.valClo" [envAt Γ, AAt Γ, getT (resB Γ)]
        dExI L K.G K.E (cloAt Γ) <| dConjI L
          (rawHyp raw₂ hLam)
          (dRwBy (evalRw K.G K.E (raw₁ ++ [.hyp hArr]) .full) <|
            K.norm <| dAllI L <| dImpI L <| withCtx fun Γ₈ Φ₈ ↦
            let xAt := atPos (Γ₈.length - 1)
            let hX := Φ₈.length - 1
            let cx' (Γ : List Tree) : Term := consT treeTy (entryAt Γ) (cxAt Γ)
            let env' (Γ : List Tree) : Term := consT treeTy (xAt Γ) (envAt Γ)
            dImpE L ih (K.byHyp hT) <| K.allEΓ cx' <| K.allEΓ env' <|
            K.impE (linkK K "ctorNest: the environment"
              (applyThm K "envTCons" (fun Γ ↦ [xAt Γ, entryAt Γ, envAt Γ, cxAt Γ, RAt Γ])
                [K.byHyp hEnv, K.byHyp hX] fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) <|
            K.impE (linkK K "ctorNest: the primitive in the context"
              (dImpI L <| withCtx fun _ Φ ↦
                let hI := Φ.length - 1
                unequalThen nAt hNe (dImpE L hN₁ (K.byHyp hI) lastFalse))) <|
            K.impE (linkK K "ctorNest: the primitive in the scope"
              (dImpI L <| withCtx fun _ Φ ↦
                let hI := Φ.length - 1
                unequalThen nAt hNe (decideIn K (fun Γ ↦ pc P "Prelude.isSome"
                    [pc P "Reader.indexOf" [nameN, scopeAt Γ]])
                  (K.hypFalse hI) (dImpE L hN₂ (K.solve 3) lastFalse)))) <|
            K.impE (linkK K "ctorNest: the body's type" (K.byHyp hSynB)) <|
            K.impE (linkK K "ctorNest: the body's resolution" (K.byHyp hResB)) <|
            K.exE <| K.conjE <| withCtx fun Γ₉ Φ₉ ↦
              let wAt := atPos (Γ₉.length - 1)
              let (dW, rW) := (Φ₉.length - 2, Φ₉.length - 1)
              denE K dW fun _ n _ st ↦
                K.conv (fun Γ ↦ succs 1 (atPos n Γ)) wAt
                  (linkK K "ctorNest: the application stable" <|
                    instNK K st (fun _ ↦ v 0) K.byNorm)
                  (linkK K "ctorNest: the application's value" (K.byHyp rW))))
        (linkK K "ctorNest: the binder abbreviated" fun Γ Φ ψ ↦
          dImpE L hPl (K.solve 3) lastFalse Γ Φ ψ)
    let d₁ ← linkK K "ctorNest: construction" cons (Ls :: treeTy :: Γ₀.tail)
      (lowered.map Internal.weaken2 ++ [Internal.weakenElem φ]) (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ₀, hyps, φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The context of the soundness at the body of a constructor's definition. -/
def bodyAllVars (T : Defs3) : List Tree :=
  let Tt := treeTy
  let Ls := list treeTy
  [Ls, Ls, Tt, Tt, Tt, Tt, Tt, Ls, T.envTy]

/-- The body of a constructor's definition, at the end {lit}`z`. -/
def ctorBody (P : Prog) (cs j nf z fs : Term) : Term :=
  pc P "Typing.tAs" [nodeT (Term.pair (numeral 1) cs),
    nodeOfForm P (pc P "Recognize.num" [j]) (Term.snd (listFold P nf z fs))]

/-- The hypotheses of the soundness at the body of a constructor's definition, at the end {lit}`z`
of the list and the flag of a variable field, in the context of {name}`bodyAllVars`: the list's end
given at every context and environment related, the fields' coherence, the typing environment's
reading of the datatype and the marker's constructor. -/
def bodyHypsAt (P : Prog) (S : Defs) (T : Defs3) (z flag : Term) : List Term :=
  let o := P.o
  let imp := Internal.Logic.imp o
  let Ls := list treeTy
  let Lss := list Ls
  let vars := bodyAllVars T
  let at_ := denAt vars
  let (Ev, cs, j, rty, dv, fs) := (at_ 6, at_ 7, at_ 8, at_ 10, at_ 13, at_ 14)
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let getT (t : Term) : Term := pc P "Prelude.get" [t]
  let Da := nodeT (Term.pair (numeral 1) cs)
  let aNode := pc P "Datatype.aNode" []
  let nameN := atomNameT aNode
  let rNode := pc P "Recognize.rNode" []
  let u (t : Term) : Term := sh 2 t
  let baseAll : Term := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o Ls (Term.lam Ls
    (imp (T.envT (u (at_ 0)) (v 1) (v 0))
      (imp (isSomeT (pc P "Typing.synIn" [u Ev, v 1, u z]))
        (imp (Term.eq (getT (pc P "Typing.synIn" [u Ev, v 1, u z])) (listOfTrees P))
          (listEndT P S (u (at_ 0)) (u (at_ 1)) (u (at_ 2)) (u (at_ 3)) (v 1) (v 0)
            (Term.snd (u (at_ 0))) (u flag) (u rty) (nilT treeTy)
            (pc P "Datatype.eraseExpr" [u z]))))))))
  let fts := repsT P dv fs
  let lastAll : Term := Internal.Logic.all o Lss (Term.lam Lss (imp
    (truth o (walkT P (Term.snd (sh 1 (at_ 0))) (sh 1 flag) (sh 1 rty) (sh 1 fts) (v 0)))
    (truth o (anyT P (pc P "Typing.ctorOk" [Term.snd (sh 3 (at_ 0)), v 1,
        leafT (call D.lab [] [sh 3 j]), v 2])
      (specsOf P (Term.snd (sh 1 (at_ 0))) (sh 1 Da))))))
  [T.numsT Ev (at_ 1), fieldAllT P Ev (at_ 1),
    notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev"
      [atomNameT (pc P "Recognize.rCons" []), at_ 1]]),
    S.allL (Term.lam treeTy (cohT P T (sh 1 (at_ 0)) (sh 1 Ev) (sh 1 dv) (v 0))) fs, baseAll,
    notTest o (pc P "Prelude.isSome" [pc P "Typing.lookupName"
      [nameN, pc P "Typing.envDefs" [Ev]]]),
    notTest o (pc P "Typing.hasName" [nameN, pc P "Typing.envNums" [Ev]]),
    numT P (at_ 1),
    notTest o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [atomNameT rNode, at_ 2]]),
    notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT rNode, at_ 1]]),
    Term.eq (getT (pc P "Typing.readTy" [Ev, rawT T Ev Da]))
      (pc P "Typing.tyData" [atomNameT Da]),
    lastAll]

/-- The statement of the soundness at the body of a constructor's definition, in the context of
{name}`bodyAllVars`, under the hypotheses {name}`bodyHypsAt`. -/
def bodyAllThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  let vars := bodyAllVars T
  let at_ := denAt vars
  ⟨0, denCtx vars, bodyHypsAt P S T (at_ 11) (at_ 9),
    formAllT P S T (at_ 0) (at_ 1) (at_ 2) (at_ 3) (at_ 6)
      (ctorBody P (at_ 7) (at_ 8) (at_ 12) (at_ 11) (at_ 14))⟩

/-- The soundness at the body of a constructor's definition ({name}`bodyAllThm`): the fields' list
({name}`ctorList`) at the end given, the node's ({name}`bodyRel`). -/
def bodyAll (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("bodyAll", fun ix E ↦ do
    let K := lamKit P S T ix E
    let P := K.P
    let L := K.L
    let thm := bodyAllThm P S T
    let (EAt, csAt, jAt, flagAt, rtyAt, zAt, nfAt, dvAt, fsAt) :=
      (atPos 6, atPos 7, atPos 8, atPos 9, atPos 10, atPos 11, atPos 12, atPos 13, atPos 14)
    let main : Deducer := dAllI L <| dAllI L <| withCtx fun Γ₁ _ ↦
      let (cxAt, envAt) := (atPos (Γ₁.length - 2), atPos (Γ₁.length - 1))
      let scopeAt (Γ : List Tree) : Term := scopeOf P (atPos 1 Γ) (cxAt Γ)
      let fixedAt (Γ : List Tree) : List Term :=
        [envAt Γ, scopeAt Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
      let lAt (Γ : List Tree) : Term := Term.snd (listFold P (nfAt Γ) (zAt Γ) (fsAt Γ))
      let ftsAt (Γ : List Tree) : Term := repsT P (dvAt Γ) (fsAt Γ)
      dImpI L <| dImpI L <| dImpI L <| dImpI L <| dImpI L <| withCtx fun _ Φ₂ ↦
      let n₂ := Φ₂.length
      let (hEnv, hN₁, hN₂) := (n₂ - 5, n₂ - 4, n₂ - 3)
      withCtx fun Γ _ ↦ dAllE L K.G K.E 4 (cxAt Γ) <| K.allEΓ envAt <|
      K.impE (K.byHyp hEnv) <|
      applyThm K "ctorList" (fun Γ ↦ [fsAt Γ, rtyAt Γ, flagAt Γ, zAt Γ, nfAt Γ, dvAt Γ, cxAt Γ,
          EAt Γ] ++ fixedAt Γ) [dHyp, K.byHyp hEnv, dHyp, K.byHyp 2, dHyp] <|
      K.impE dHyp <| withCtx fun _ Φ₄ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₄ 10) .full) 10 <|
      applyThm K "bodyRel" (fun Γ ↦ [rtyAt Γ, flagAt Γ, ftsAt Γ, lAt Γ, jAt Γ, csAt Γ, cxAt Γ,
          EAt Γ] ++ fixedAt Γ)
        [K.byHyp hN₁, K.byHyp 5, K.byHyp 6, dHyp, K.byHyp hN₂, K.byHyp 8, K.byHyp 9,
          dHyp, K.byNorm, dHyp] <|
      K.impE dHyp dHyp
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "bodyAll: not proved" fun _ ↦ none
    pure (thm, d))

/-- A name equal to that of a constructor's field begins with the character of the implementation's
names: the equality's soundness, the first character's label compared at each side. In the context
of the name and the field's number. -/
def fieldNameHead (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("fieldNameHead", fun ix E ↦ do
    let K := lamKit P S T ix E
    let P := K.P
    let o := P.o
    let eqT ← primT Kernel.Prim.eq
    let equalT ← primT Kernel.Prim.equal
    let childT ← primT Kernel.Prim.child
    let (y, k) := (v 0, v 1)
    let n := atomNameT (fieldAtomT P k)
    let headIs (t : Term) : Term :=
      apps eqT [leafT (call D.lab [] [apps childT [t, leafT bnilT]]), leafT (numeral 37)]
    let thm : Internal.Thm := ⟨0, [treeTy, treeTy], [truth o (apps equalT [n, y])],
      truth o (headIs y)⟩
    let nAt (Γ : List Tree) : Term := atomNameT (fieldAtomT P (atPos 0 Γ))
    let some d := (K.cutThm "equalSymm" (fun Γ ↦ [atPos 1 Γ, nAt Γ]) <| K.impE (K.byHyp 0) <|
        withCtx fun _ Φ ↦
        let h := Φ.length - 1
        K.cutThm "equalSound" (fun Γ ↦ [atPos 1 Γ]) <| K.allEΓ nAt <| K.impE (K.byHyp h) <|
        normLastK K <| linkK K "fieldNameHead: the head" (K.solve 3)) thm.ctx thm.hyps thm.concl
      | dbgTrace "fieldNameHead: not proved" fun _ ↦ none
    pure (thm, d))

/-- The expansion of the numeral abbreviations fixes the characters of a field's atom where it fixes
those of its number. In the context of the number's characters and the numeral abbreviations. -/
def fixedField (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("fixedField", fun ix E ↦ do
    let K₀ := lamKit P S T ix E
    let unfolded := K₀.P.folded.filter (· != "charsFixed")
    let K : Kit := { K₀ with P := { K₀.P with folded := unfolded } }
    let P := K.P
    let (cs, nums) := (v 0, v 1)
    let fn := Term.lam treeTy (pc P "Reader.expandNums" [sh 1 nums, v 0])
    let thm : Internal.Thm := ⟨0, [list treeTy, list treeTy],
      [truth P.o (pc P "charsFixed" [fn, cs])],
      truth P.o (pc P "charsFixed" [fn, consT treeTy (leafT (numeral 37))
        (consT treeTy (leafT (numeral 102)) cs)])⟩
    let xAt (Γ : List Tree) : Term := node0 (consT treeTy (leafT (numeral 37))
      (consT treeTy (leafT (numeral 102)) (atPos 1 Γ)))
    let main : Deducer :=
      K.cutThm "charsFixedEq" (fun Γ ↦ [atPos 1 Γ, atPos 0 Γ]) <| K.impE (K.byHyp 0) <|
      normLastK K <| K.cutThm "equalRefl" (fun Γ ↦ [xAt Γ]) <| withCtx fun _ Φ ↦
      let h := Φ.length - 1
      let rs (Φ : List Term) : List Internal.NormRule := K.rules Φ ++ [.delta (T.argIdx 3)]
      dRwHyp (evalRw K.G K.E (rs Φ) .full) h <|
      linkK K "fixedField: the characters" fun Γ Φ ψ ↦
        dRwBy (evalRw K.G K.E (rs Φ) .full) dHyp Γ Φ ψ
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "fixedField: not proved" fun _ ↦ none
    pure (thm, d))

/-- The binders of a constructor's fields, by the right fold of its definition. -/
def binderFold (P : Prog) (nf fs : Term) : Term :=
  let Ls := list treeTy
  let C := prod treeTy Ls
  let addT := (primT Kernel.Prim.add).getD Term.star
  let subT := (primT Kernel.Prim.sub).getD Term.star
  Term.snd (foldrT treeTy C (Term.lam treeTy (Term.lam C (Term.pair
      (apps addT [Term.fst (v 0), leafT (numeral 1)])
      (consT treeTy (listNode [fieldAtomT P (apps subT [apps subT [sh 2 nf, leafT (numeral 1)],
        Term.fst (v 0)]), v 1]) (Term.snd (v 0))))))
    (Term.pair (leafT bnilT) (nilT treeTy)) fs)

/-- That an annotation's erasure reads as a type. Beneath the annotation {lit}`F`. -/
def readOkT (P : Prog) (nums tys F : Term) : Term :=
  Internal.Logic.ex P.o treeTy (Term.lam treeTy (Term.eq (pc P "Reader.readType" [sh 1 tys,
    pc P "Reader.expandNums" [sh 1 nums, pc P "Datatype.eraseExpr" [sh 1 F]]])
    (pc P "Prelude.some" [v 0])))

/-- The binders of a constructor's fields are binders ({name}`binderOkT`), each annotation reading
as a type: by induction on the fields, the atom's properties from {name}`fieldAllT`, that it is
named by no keyword by {name}`fieldNameHead`. In the context of the fields, the number of the
fields, the typing environment and the abbreviations. -/
def fieldBinders (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("fieldBinders", fun ix E ↦ do
    let K := lamKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let imp := Internal.Logic.imp o
    let Ls := list treeTy
    let Γ₀ := [Ls, treeTy, T.envTy, Ls, Ls]
    let (fs, nf, Ev, nums, tys) := (v 0, v 1, v 2, v 3, v 4)
    let oks (xs : Term) : Term := S.allL
      (Term.lam treeTy (binderOkT P (sh 1 nums) (sh 1 tys) (v 0))) xs
    let reads (xs : Term) : Term := S.allL
      (Term.lam treeTy (readOkT P (sh 1 nums) (sh 1 tys) (v 0))) xs
    let hyps := [fieldAllT P Ev nums]
    let φ := imp (reads fs) (oks (binderFold P nf fs))
    let some lowered := Internal.lowerHyps P.G 0 Γ₀.tail hyps
      | dbgTrace "fieldBinders: the hypotheses" fun _ ↦ none
    let d₀ ← (dImpI L (K.solve 3)) Γ₀.tail lowered
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let (numsAt, nfAt, fAt, tlAt) := (atPos 1, atPos 3, atPos 4, atPos 5)
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let lastHyp : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let kAt (Γ : List Tree) : Term :=
      let subT := (primT Kernel.Prim.sub).getD Term.star
      let C := prod treeTy Ls
      apps subT [apps subT [nfAt Γ, leafT (numeral 1)], Term.fst (foldrT treeTy C
        (Term.lam treeTy (Term.lam C (Term.pair
          (apps ((primT Kernel.Prim.add).getD Term.star) [Term.fst (v 0), leafT (numeral 1)])
          (consT treeTy (listNode [fieldAtomT P (apps subT [apps subT [sh 2 (nfAt Γ),
            leafT (numeral 1)], Term.fst (v 0)]), v 1]) (Term.snd (v 0))))))
        (Term.pair (leafT bnilT) (nilT treeTy)) (tlAt Γ))]
    let notName (y : Term) : Deducer := dImpI L <|
      applyThm K "fieldNameHead" (fun Γ ↦ [y, kAt Γ]) [lastHyp] lastFalse
    let cons : Deducer := dImpI L <| withCtx fun _ Φ₁ ↦
      let hR := Φ₁.length - 1
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₁ hR) .full) hR <| K.conjE <| withCtx fun _ Φ₂ ↦
      let (hF, hT) := (Φ₂.length - 2, Φ₂.length - 1)
      dExE L K.G K.E hF <| withCtx fun Γ₃ Φ₃ ↦
      let AAt := atPos (Γ₃.length - 1)
      let hA := Φ₃.length - 1
      withCtx fun Γ _ ↦ dAllE L K.G K.E 0 (kAt Γ) <| K.conjE <| K.conjE <| K.conjE <| K.conjE <|
      withCtx fun _ Φ₄ ↦
      let n₄ := Φ₄.length
      let (hPl, hFx) := (n₄ - 8, n₄ - 6)
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₄ hA) .full) hA <|
      K.norm <| dConjI L
        (fun Γ Φ ψ ↦ dExI L K.G K.E (fieldChars P (kAt Γ)) (dExI L K.G K.E (fAt Γ)
          (dExI L K.G K.E (AAt Γ) (K.norm <| dConjI L
            (linkK K "fieldBinders: the binder" K.byNorm) <| dConjI L
            (linkK K "fieldBinders: not abbreviated" (K.byHyp hPl)) <| dConjI L
            (linkK K "fieldBinders: fixed" (applyThm K "fixedField"
              (fun Γ ↦ [pc P "Typing.decimalChars" [kAt Γ], numsAt Γ]) [K.byHyp hFx] lastHyp)) <|
            dConjI L
            (linkK K "fieldBinders: not the representation"
              (notName (pc P "Typing.kwRep" []))) <| dConjI L
            (linkK K "fieldBinders: not decoding" (notName (pc P "Typing.kwDecode" []))) <| dConjI L
            (linkK K "fieldBinders: not a datum" (notName (pc P "Typing.kwDatum" []))) <| dConjI L
            (linkK K "fieldBinders: not the primitive" <| dImpI L <|
              K.cutThm "equalSymm" (fun Γ ↦ [atomNameT (fieldAtomT P (kAt Γ)),
                  atomNameT (pc P "Datatype.aNode" [])]) <| K.impE lastHyp <|
              applyThm K "fieldNameHead" (fun Γ ↦ [atomNameT (pc P "Datatype.aNode" []), kAt Γ])
                [lastHyp] lastFalse)
            (linkK K "fieldBinders: the annotation" K.byNorm)))) Γ Φ ψ)
        (dImpE L 1 (K.byHyp hT) lastHyp)
    let d₁ ← linkK K "fieldBinders: construction" cons (Ls :: treeTy :: Γ₀.tail)
      (lowered.map Internal.weaken2 ++ [Internal.weakenElem φ]) (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ₀, hyps, φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The hypotheses of a definition's abstractions around its body beyond those of the body: the
abstractions' keyword not abbreviated and the fields' annotations reading as types. -/
def nestHyps (P : Prog) (S : Defs) (T : Defs3) : List Term :=
  let o := P.o
  let at_ := denAt (bodyAllVars T)
  [notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev"
      [atomNameT (pc P "Recognize.rLam" []), at_ 1]]),
    S.allL (Term.lam treeTy (readOkT P (sh 1 (at_ 1)) (sh 1 (at_ 3)) (v 0))) (at_ 14)]

/-- A constructor without a variable field is sound: its body's soundness ({name}`bodyAll`) at the
end of the list ({name}`baseNil`), its abstractions' ({name}`ctorNest`) over the fields' binders
({name}`fieldBinders`). In the context of {name}`bodyAllVars`. -/
def ctorPlain (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("ctorPlain", fun ix E ↦ do
    let K := lamKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let vars := bodyAllVars T
    let at_ := denAt vars
    let z := pc P "Datatype.sx2" [pc P "Datatype.aNil" [], pc P "Datatype.aT" []]
    let flag := leafT bnilT
    let plainOf (a : Term) : Term := notTest o (pc P "Prelude.isSome"
      [pc P "Reader.lookupAbbrev" [atomNameT a, at_ 1]])
    let hBody := bodyHypsAt P S T z flag
    let hyps := hBody ++ nestHyps P S T ++
      [plainOf (pc P "Recognize.rNil" []), plainOf (pc P "Recognize.rT" [])]
    let body := ctorBody P (at_ 7) (at_ 8) (at_ 12) z (at_ 14)
    let thm : Internal.Thm := ⟨0, denCtx vars, hyps,
      formAllT P S T (at_ 0) (at_ 1) (at_ 2) (at_ 3) (at_ 6)
        (nestT P (binderFold P (at_ 12) (at_ 14)) body)⟩
    let n := hBody.length
    let (EAt, csAt, jAt, rtyAt, nfAt, dvAt, fsAt) :=
      (atPos 6, atPos 7, atPos 8, atPos 10, atPos 12, atPos 13, atPos 14)
    let bodyAt (Γ : List Tree) : Term := ctorBody P (csAt Γ) (jAt Γ) (nfAt Γ) z (fsAt Γ)
    let baseD : Deducer := dAllI L <| dAllI L <| withCtx fun Γ₁ _ ↦
      let (cxAt, envAt) := (atPos (Γ₁.length - 2), atPos (Γ₁.length - 1))
      let fixedAt (Γ : List Tree) : List Term :=
        [envAt Γ, scopeOf P (atPos 1 Γ) (cxAt Γ), atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
      dImpI L <| dImpI L <| dImpI L <|
      applyThm K "baseNil" (fun Γ ↦ [rtyAt Γ, cxAt Γ] ++ fixedAt Γ)
        [K.byHyp (n + 2), K.byHyp (n + 3)] dHyp
    let prems : List Deducer := (List.range hBody.length).map fun i ↦
      if i = 4 then linkK K "ctorPlain: the end" baseD else fun Γ Φ ψ ↦ dHyp Γ Φ ψ
    let main : Deducer :=
      applyThm K "bodyAll" (fun Γ ↦ [fsAt Γ, dvAt Γ, nfAt Γ, z, rtyAt Γ, flag, jAt Γ, csAt Γ,
        EAt Γ, atPos 5 Γ, atPos 4 Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]) prems <|
      applyThm K "ctorNest" (fun Γ ↦ [binderFold P (nfAt Γ) (fsAt Γ), bodyAt Γ, EAt Γ, atPos 3 Γ,
          atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]) [dHyp, dHyp, dHyp] <|
      applyThm K "fieldBinders" (fun Γ ↦ [fsAt Γ, nfAt Γ, EAt Γ, atPos 1 Γ, atPos 3 Γ]) [dHyp] <|
      K.impE dHyp <| withCtx fun _ Φ ↦
      dImpE L (Φ.length - 3) dHyp dHyp
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "ctorPlain: not proved" fun _ ↦ none
    pure (thm, d))

/-- A predicate of each of two lists holds of their concatenation: by induction on the first. In the
context of the first and the second, under the predicate. -/
def allAppend (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("allAppend", fun ix E ↦ do
    let K := lamKit P S T ix E
    let P := K.P
    let L := K.L
    let imp := Internal.Logic.imp P.o
    let Ls := list treeTy
    let Pr := exp treeTy omega
    -- under the predicate: the predicate v0, the first v1, the second v2
    let φ := Internal.Logic.all P.o Pr (Term.lam Pr (imp (S.allL (v 0) (v 1))
      (imp (S.allL (v 0) (v 2)) (S.allL (v 0) (pc P "Prelude.append" [v 1, v 2])))))
    let lastHyp : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let d₀ ← (dAllI L <| dImpI L <| dImpI L lastHyp) [Ls] []
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let cons : Deducer := dAllI L <| withCtx fun Γ₁ _ ↦
      let prAt := atPos (Γ₁.length - 1)
      dImpI L <| dImpI L <| withCtx fun _ Φ₂ ↦
      let (hA, hB) := (Φ₂.length - 2, Φ₂.length - 1)
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₂ hA) .full) hA <| K.conjE <| withCtx fun _ Φ₃ ↦
      let (hH, hT) := (Φ₃.length - 2, Φ₃.length - 1)
      K.norm <| dConjI L (K.byHyp hH)
        (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (prAt Γ) (K.impE (K.byHyp hT) <| K.impE (K.byHyp hB)
          lastHyp) Γ Φ ψ)
    let d₁ ← linkK K "allAppend: construction" cons [Ls, treeTy, Ls]
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [Ls, Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The binder of a variable field is a binder ({name}`binderOkT`), its annotation reading as a type
and its atom named by no abbreviation. In the context of the annotation, the numeral abbreviations
and the type abbreviations. -/
def restBinder (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("restBinder", fun ix E ↦ do
    let K := lamKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let (F, nums, tys) := (v 0, v 1, v 2)
    let aRest := pc P "Datatype.aRest" []
    let thm : Internal.Thm := ⟨0, [treeTy, Ls, Ls],
      [notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT aRest, nums]]),
        readOkT P nums tys F],
      binderOkT P nums tys (listNode [aRest, F])⟩
    let cs : Term := call D.children [] [aRest]
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let main : Deducer := dExE L K.G K.E 1 <| normLastK K <| withCtx fun Γ₁ _ ↦
      let AAt := atPos (Γ₁.length - 1)
      dExI L K.G K.E cs <| dExI L K.G K.E (atPos 2 Γ₁) <| dExI L K.G K.E (AAt Γ₁) <|
      K.norm <| dConjI L (linkK K "restBinder: the binder" K.byNorm) <| dConjI L (K.byHyp 0) <|
      dConjI L (linkK K "restBinder: fixed" fun Γ Φ ψ ↦
        dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta (P.idx "charsFixed"), .delta (T.argIdx 3)])
          .full) (K.solve 3) Γ Φ ψ) <|
      dConjI L (dImpI L lastFalse) <| dConjI L (dImpI L lastFalse) <|
      dConjI L (dImpI L lastFalse) <| dConjI L (dImpI L lastFalse) <|
      linkK K "restBinder: the annotation" K.byNorm
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "restBinder: not proved" fun _ ↦ none
    pure (thm, d))

/-- A constructor with a variable field is sound: its body's soundness ({name}`bodyAll`) at the end
of the list ({name}`baseVar`), its abstractions' ({name}`ctorNest`) over the fields' binders
({name}`fieldBinders`) and the variable field's ({name}`restBinder`). The variable field's
annotation is the variable of position 9 of {name}`bodyAllVars`. -/
def ctorVar (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("ctorVar", fun ix E ↦ do
    let K := lamKit P S T ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let imp := Internal.Logic.imp o
    let childT ← primT Kernel.Prim.child
    let vars := bodyAllVars T
    let at_ := denAt vars
    let aRest := pc P "Datatype.aRest" []
    let (Ev, F, rty) := (at_ 6, at_ 9, at_ 10)
    let z := pc P "Typing.tOf" [F, aRest]
    let flag := leafT (numeral 1)
    let first (t : Term) : Term := apps childT [t, leafT bnilT]
    let readOf (Ev F : Term) : Term :=
      pc P "Prelude.get" [pc P "Typing.readTy" [Ev, rawT T Ev F]]
    let hBody := bodyHypsAt P S T z flag
    let hNest := nestHyps P S T
    let hRest : List Term :=
      [notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT aRest, at_ 1]])] ++
      atomFreeT P Ev aRest ++
      [Internal.Logic.all o treeTy (Term.lam treeTy (imp
        (Term.app (T.relT (sh 1 (at_ 0)) (first (readOf (sh 1 Ev) (sh 1 F)))) (quoteV P (v 0)))
        (truth o (pc P "Typing.fieldOk" [Term.snd (sh 1 (at_ 0)), sh 1 rty,
          pc P "Typing.memberships" [Term.snd (sh 1 (at_ 0)), v 0]])))),
        readOkT P (at_ 1) (at_ 3) F]
    let hyps := hBody ++ hNest ++ hRest
    let body := ctorBody P (at_ 7) (at_ 8) (at_ 12) z (at_ 14)
    let bindersOf (nf fs F : Term) : Term := pc P "Prelude.append" [binderFold P nf fs,
      consT treeTy (listNode [aRest, F]) (nilT treeTy)]
    let thm : Internal.Thm := ⟨0, denCtx vars, hyps,
      formAllT P S T (at_ 0) (at_ 1) (at_ 2) (at_ 3) Ev
        (nestT P (bindersOf (at_ 12) (at_ 14) F) body)⟩
    let n := hBody.length + hNest.length
    let (EAt, csAt, jAt, FAt, rtyAt, nfAt, dvAt, fsAt) :=
      (atPos 6, atPos 7, atPos 8, atPos 9, atPos 10, atPos 12, atPos 13, atPos 14)
    let zAt (Γ : List Tree) : Term := pc P "Typing.tOf" [FAt Γ, aRest]
    let bodyAt (Γ : List Tree) : Term := ctorBody P (csAt Γ) (jAt Γ) (nfAt Γ) (zAt Γ) (fsAt Γ)
    let baseD : Deducer := dAllI L <| dAllI L <| withCtx fun Γ₁ _ ↦
      let (cxAt, envAt) := (atPos (Γ₁.length - 2), atPos (Γ₁.length - 1))
      let fixedAt (Γ : List Tree) : List Term :=
        [envAt Γ, scopeOf P (atPos 1 Γ) (cxAt Γ), atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
      dImpI L <| withCtx fun _ Φ ↦
      let hEnv := Φ.length - 1
      applyThm K "baseVar" (fun Γ ↦ [FAt Γ, rtyAt Γ, cxAt Γ, EAt Γ] ++ fixedAt Γ)
        [dHyp, K.byHyp hEnv, dHyp, dHyp, dHyp, dHyp, dHyp] dHyp
    let prems : List Deducer := (List.range hBody.length).map fun i ↦
      if i = 4 then linkK K "ctorVar: the end" baseD else fun Γ Φ ψ ↦ dHyp Γ Φ ψ
    let okP (Γ : List Tree) : Term := Term.lam treeTy
      (binderOkT P (sh 1 (atPos 1 Γ)) (sh 1 (atPos 3 Γ)) (v 0))
    let main : Deducer :=
      applyThm K "bodyAll" (fun Γ ↦ [fsAt Γ, dvAt Γ, nfAt Γ, zAt Γ, rtyAt Γ, flag, jAt Γ, csAt Γ,
        EAt Γ, atPos 5 Γ, atPos 4 Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]) prems <|
      applyThm K "ctorNest" (fun Γ ↦ [bindersOf (nfAt Γ) (fsAt Γ) (FAt Γ), bodyAt Γ, EAt Γ,
          atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]) [dHyp, dHyp, dHyp] <|
      withCtx fun _ Φ₀ ↦
      let hN := Φ₀.length - 1
      applyThm K "fieldBinders" (fun Γ ↦ [fsAt Γ, nfAt Γ, EAt Γ, atPos 1 Γ, atPos 3 Γ]) [dHyp] <|
      K.impE dHyp <|
      applyThm K "restBinder" (fun Γ ↦ [FAt Γ, atPos 1 Γ, atPos 3 Γ])
        [K.byHyp n, K.byHyp (n + 5)] <|
      withCtx fun _ Φ₂ ↦
      let hOne := Φ₂.length - 1
      K.cutThm "allAppend" (fun Γ ↦ [binderFold P (nfAt Γ) (fsAt Γ),
          consT treeTy (listNode [aRest, FAt Γ]) (nilT treeTy)]) <|
      K.allEΓ okP <| K.impE dHyp <|
      K.impE (linkK K "ctorVar: the variable field's binder" (K.norm (dConjI L (K.byHyp hOne)
        (K.solve 2)))) <|
      withCtx fun _ Φ₃ ↦
      dImpE L hN (K.byHyp (Φ₃.length - 1)) dHyp
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "ctorVar: not proved" fun _ ↦ none
    pure (thm, d))

/-- The development of the abstractions over the constructors' fields. -/
def constructorNestDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [ctorNest P S T, bodyAll P S T, fieldNameHead P S T, fixedField P S T, fieldBinders P S T,
    ctorPlain P S T, allAppend P S T, restBinder P S T, ctorVar P S T]

/-- The development of {name}`constructorNestDev`, after that of {name}`constructorLamDev`, stored
as the certificate {lit}`datatype-constructor-nest`. -/
def constructorNestCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := walkAfter P S T | throw "the base is not stated"
  certifyAfter P (names ++ (walkDev P S T).map (·.1) ++ (recognizerDev P S T).map (·.1) ++
    (recognizerFoldDev P S T).map (·.1) ++ (constructorDev P S T).map (·.1) ++
    (constructorBodyDev P S T).map (·.1) ++ (constructorLamDev P S T).map (·.1))
    "datatype-constructor-nest" (constructorNestDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
