/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeClauses
public import GebTests.Prototypes.FreeTopos.DatatypeLists
public meta import GebTests.Prototypes.FreeTopos.DatatypeClauses -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at a case analysis

The soundness of the datatype language's stage-1 compiler at a case analysis: the typing's,
the erasure's and the reader's steps at the expansion's checked node of a case analysis, the
scrutinee bound once and the chain of its clauses
({name}`GebTests.Prototypes.FreeTopos.Datatypes.chain`) in its scope.

## Main definitions

* {lit}`caseSoundCertificates` — the development, stored as the certificate
  {lit}`datatype-case-sound`.

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

/-- The context of the soundness at an expanded case analysis: the bodies' forms v0, the
clauses' metadata v1, the scrutinee's form v2 and the datatype's atom v3. -/
def caseCoreCtx : List Tree := [list treeTy, list treeTy, treeTy, treeTy]

/-- The expanded case analysis of {name}`caseCoreCtx`, the typing's node of its parts. -/
def caseNode (P : Prog) : Term :=
  pc P "Typing.tCase" [consT treeTy (v 3) (consT treeTy (v 2)
    (consT treeTy (pc P "Typing.tList" [v 1]) (v 0)))]

/-- A clause's metadata's shape, as the expansion writes it: a list, whose second and third
elements are lists. -/
def shapeMeta (P : Prog) : Term :=
  let isList (t : Term) : Term := truth P.o (pc P "Datatype.isListTx" [t])
  let nthE (i : ℕ) : Term :=
    pc P "Datatype.nthTx" [pc P "Datatype.elems" [v 0], leafT (numeral i)]
  Term.lam treeTy (Internal.Logic.conj P.o (isList (v 0))
    (Internal.Logic.conj P.o (isList (nthE 1)) (isList (nthE 2))))

/-- The statement of the soundness at an expanded case analysis ({name}`caseNode`): where it holds
at the scrutinee's form and at each body's, and the metadata are shaped as the expansion writes them
({name}`shapeMeta`), it holds at the case analysis. -/
def caseCoreThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  let φ := expandedφ P S T
  ⟨0, caseCoreCtx, [Internal.instTerm [] [v 2] φ, S.allL (Term.lam treeTy φ) (v 0),
    S.allL (shapeMeta P) (v 1)], Internal.instTerm [] [caseNode P] φ⟩

/-- The expansion of the numeral abbreviations at the scrutinee's binder, its name not
abbreviated, is the binder. In the context of the numeral abbreviations. -/
def scrutNums (P : Prog) (S : Defs) (T : Defs3) : Step :=
  builderEq "aSNums" P S [list treeTy]
    [pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [scrutineeName P, v 0]]]
    (pc P "Reader.expandNums" [v 0, pc P "Datatype.aS" []]) (fun _ _ _ ↦ [.delta (T.argIdx 3)])
    (pc P "Datatype.aS" [])

/-- The resolution of the scrutinee's binding, present, gives the body's, in the scope extended by
the binder's name, and the term's, present, and is the application of the abstraction over the
annotation's type of the body's to the term's ({lit}`letRes`): in the context of the body v0, the
term v1, the scope v2, the type abbreviations v3 and the names v4. Proved by the reader's case of
a binding, its parts' presence decided, absent refuting the hypothesis. -/
def scrutLet (P : Prog) (S : Defs) : Step :=
  ("scrutLet", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let L := K.L
    let o := P.o
    let Γ := [treeTy, treeTy, list treeTy, list treeTy, list treeTy]
    let aS := pc P "Datatype.aS" []
    let res (t sc : Term) : Term := pc P "Reader.resolve" [v 3, v 4, t, sc]
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let whole := res (pc P "Datatype.sLet" [aS, pc P "Datatype.aT" [], v 1, v 0]) (v 2)
    let rA := pc P "Reader.readType" [v 3, pc P "Datatype.aT" []]
    let rB := res (v 0) (consT treeTy (pc P "Reader.nameOf" [aS]) (v 2))
    let rE := res (v 1) (v 2)
    let concl := Internal.Logic.conj o (isSomeT rB) (Internal.Logic.conj o (isSomeT rE)
      (Term.eq (get whole) (pc P "Reader.app" [pc P "Reader.node2"
        [leafT (numeral Kernel.Label.lam), get rA, get rB], get rE])))
    let a : Internal.Thm := ⟨0, Γ, [isSomeT whole], concl⟩
    -- each part's presence decided, the hypothesis refuted where any is absent
    let parts : List Term → Bool → Deducer → Deducer := fun opts absent k ↦
      opts.foldr (fun opt rest absent ↦
          decideOpt K (fun Γ ↦ sh (Γ.length - 5) opt) (rest true) (rest absent)
            (minimal := true))
        (fun absent ↦ if absent then
            linkK K "scrutLet: a part absent" fun Γ Φ ψ ↦
              (K.hypFalse 1 Γ Φ ψ).orElse fun _ ↦ K.hypFalse 0 Γ Φ ψ
          else k) absent
    let some d := (dRwHyp (evalRw K.G K.E (K.rulesEx [] 0 ++ [.thm (ix "letRes") []]) .full) 0 <|
        parts [rA, rE, rB] false <|
        linkK K "scrutLet: the parts" (dConjI L (K.solve 3) (dConjI L (K.solve 3)
          (fun Γ Φ ψ ↦ dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0
            (K.rules Φ ++ [.thm (ix "letRes") []]) Γ (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ))))
        a.ctx a.hyps a.concl
      | dbgTrace "scrutLet: not proved" fun _ ↦ none
    pure (a, d))

/-- A value related at the datatype a form names is a member's quotation, the converse of
{lit}`relTDatum`: where the relation's markers are the typing environment's, the type {lit}`y` a
datatype the environment declares and the form {lit}`D` names by its own name
({lit}`Typing.namesData`), and the value {lit}`x` related at {lit}`y`, the value is the quotation of
a member of the datatype {lit}`D` names. In the context of the value, the form, the type, the
environment and the relation's context. -/
def relTDataMemberThm (P : Prog) (T : Defs3) : Internal.Thm :=
  let o := P.o
  ⟨0, [treeTy, treeTy, treeTy, T.envTy, Defs3.ctxTy],
    [Term.eq (Term.snd (v 4)) (pc P "Typing.envMs" [v 3]),
      truth o (pc P "Typing.namesData" [v 3, v 2, v 1]),
      Term.app (T.relT (v 4) (v 2)) (v 0)],
    Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
      (Term.eq (v 1) (pc P "Eval.valQuote" [v 0]))
      (truth o (pc P "Typing.memberOf" [pc P "Typing.envMs" [v 4], v 2, v 0]))))⟩

/-- A value related at the datatype a form names is a member's quotation
({name}`relTDataMemberThm`): as {lit}`relTDatum`, the type a node, its label decided by the test of
its naming, and the name's equality with the form's characters by the equality's soundness; at the
label of datatypes the relation unfolded in its hypothesis, its witness the member. -/
def relTDataMember (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relTDataMember", fun ix E ↦ do
    let K := datumKit P S ix E ((vocab3 ++ ["relTTree"] ++ relRebuildNames).filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size)
    let L := K.L
    let a := relTDataMemberThm P T
    let childrenT ← primT Kernel.Prim.children
    let namesD := Internal.NormRule.delta (P.idx "Typing.namesData")
    let tests (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 1 ++ [namesD]) .full) 1
        (K.splitHyp (Φ.length) (fun Γ Φ ψ ↦ (anyFalse K Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ) 16)
        Γ Φ ψ
    -- the relation's hypothesis unfolded at the datatype, its witness the member
    -- without the name's equation of index ex, so that the relation's rebuilding of the name is
    -- the name before it is rewritten
    let witness (ex : Option ℕ) : Deducer := fun Γ Φ ψ ↦
      let rs := (K.rulesEx Φ 2).filter fun r ↦ match r, ex with
        | .hyp j, some e => j ≠ e
        | _, _ => true
      dRwHyp (evalRw K.G K.E (rs ++ [.delta T.q]) .full) 2 (K.exE <| K.conjE
        fun Γ Φ ψ ↦
        let pt := Γ.length - 1
        let iM := Φ.length - 1
        linkK K "relTDataMember: the witness"
          (dExI L K.G K.E (atPos pt Γ) (dConjI L (K.solve 3)
            -- the markers' equation, the first hypothesis, which supplies no rule, as one
            (linkK K "relTDataMember: the membership" fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ iM ++ [.hyp 0]) .full) iM
                (dRwBy (evalRw K.G K.E (K.rules Φ ++ [.hyp 0]) .full) dHyp) Γ Φ ψ))) Γ Φ ψ) Γ Φ ψ
    let some d := (linkK K "relTDataMember" <| K.treeNode (atPos 2 a.ctx) <| fun Γ Φ ψ ↦
        let body : Deducer := fun Γ Φ ψ ↦ (K.treeNode (atPos 3 Γ) <| tests <|
          linkK K "relTDataMember: a datatype" <| fun Γ Φ ψ ↦ do
          let some (x, y) := (List.range Φ.length).reverse.findSome? fun h ↦ do
              let t ← Φ[h]?
              let (n, _) ← evalRw K.G K.E (K.rulesEx Φ h) .full Γ Φ t
              equalArgs n
            | traceK K "relTDataMember: no equality" Γ Φ ψ
          let attempt (x y : Term) : Deducer :=
            K.cutThm "equalSound" (fun _ ↦ [x]) <| K.allEΓ (fun _ ↦ y) <|
            K.impE (K.solve 3) <| fun Γ Φ ψ ↦
            let hEq := Φ.length - 1
            K.image hEq (fun t ↦ apps childrenT [t]) (witness (some hEq)) Γ Φ ψ
          (attempt x y Γ Φ ψ).orElse fun _ ↦ attempt y x Γ Φ ψ) Γ Φ ψ
        let none' : Deducer := fun Γ Φ ψ ↦ (K.treeNode (atPos 3 Γ) <| tests <|
          linkK K "relTDataMember: no children" <| fun Γ Φ ψ ↦
          K.listCase treeTy (atPos 8 Γ) (witness none) (anyFalse K) Γ Φ ψ) Γ Φ ψ
        K.listCase treeTy (atPos 6 Γ) none' body Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "relTDataMember: not proved" fun _ ↦ none
    pure (a, d))

/-- A conjunction of tests true makes each true: in the context of the right test and the left.
Proved by deciding each, false refuting the hypothesis. -/
def andParts (P : Prog) (S : Defs) : Step :=
  ("andParts", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let o := P.o
    let Γ := [treeTy, treeTy]
    let a : Internal.Thm := ⟨0, Γ, [truth o (pc P "Prelude.and" [v 1, v 0])],
      Internal.Logic.conj o (truth o (v 1)) (truth o (v 0))⟩
    let some d := decideIn K (fun Γ ↦ atPos 0 Γ) (K.hypFalse 0)
        (decideIn K (fun Γ ↦ atPos 1 Γ) (K.hypFalse 0) (dConjI K.L (K.solve 3) (K.solve 3)))
        a.ctx a.hyps a.concl
      | dbgTrace "andParts: not proved" fun _ ↦ none
    pure (a, d))

/-- The statement that each element of a list node that is a source form is
{name}`fixedAtom`: in the context of the elements v0 and the numeral abbreviations v1. -/
def fixedAllφ (P : Prog) (S : Defs) : Term :=
  Internal.Logic.imp P.o (srcAt P (v 1) (pc P "Typing.tList" [v 0]))
    (S.allL (fixedAtom P (v 1)) (v 0))

/-- Each element of a list node that is a source form is {name}`fixedAtom` ({name}`fixedAllφ`): by
induction on the elements, the test of source forms split at the head ({lit}`srcCons`), each part
decided, false refuting it; the head, an atom, its label decided, its test its characters'. -/
def fixedAll (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("fixedAll", fun ix E ↦ do
    let K : Kit := ⟨walkProg P, S, E, ix, (vocab3 ++ ["srcCons"]).filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size⟩
    let L := K.L
    let P := K.P
    let φ := fixedAllφ P S
    let Γ := [list treeTy, list treeTy]
    let d₀ ← dImpI L (K.solve 3) Γ.tail [] (Term.subst φ (Internal.instVar (nilT treeTy)))
    -- a construction: the rest v0, the head v1; the test at the list the test at the head and
    -- at the rest ({lit}`srcCons`), each true ({name}`andParts`); the goal the rest's and the
    -- head's
    let srcT (x : Term) (Γ : List Tree) : Term :=
      pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [sh 1 (atPos 0 Γ), v 0]), x]
    let cons : Deducer := dImpI L fun Γ Φ ψ ↦
      let iS := Φ.length - 1
      let (px, pr) := (Γ.length - 2, Γ.length - 1)
      -- the head an atom, its test, the source forms' step unfolded, its characters'
      let head (iX : ℕ) : Deducer := linkK K "fixedAll: the head fixed" <| dImpI L <|
        K.treeNode (atPos px Γ) <| normLastK K fun Γ Φ ψ ↦
          dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
            if bs.map Oitavem.rank == some 1 then
              linkK K "fixedAll: an atom" fun Γ Φ ψ ↦
                dRwHyp (evalRw K.G K.E (K.rulesEx Φ iX ++ [.delta (T.argIdx 5)]) .full) iX
                  (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
            else
              linkK K s!"fixedAll: the label {bs.map Oitavem.rank}" fun Γ Φ ψ ↦
                (List.range Φ.length).reverse.findSome? fun h ↦ K.hypFalse h Γ Φ ψ)
            3 [] (v 1) Γ Φ ψ
      let rest (iR : ℕ) : Deducer := linkK K "fixedAll: the rest fixed" <|
        dImpE L 0 (K.byHyp iR) fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
      (applyThm K "andParts" (fun Γ ↦ [srcT (pc P "Typing.tList" [atPos pr Γ]) Γ,
          srcT (atPos px Γ) Γ]) [linkK K "fixedAll: the test split" (K.byHyp iS)] <|
        K.conjE fun Γ Φ ψ ↦
        let iR := Φ.length - 1
        let either : Deducer := fun Γ Φ ψ ↦ (rest iR Γ Φ ψ).orElse fun _ ↦ head (iR - 1) Γ Φ ψ
        linkK K "fixedAll: the parts" (K.norm (dConjI L either either)) Γ Φ ψ) Γ Φ ψ
    let some d₁ := linkK K "fixedAll: a construction" cons (list treeTy :: treeTy :: Γ.tail)
        [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "fixedAll: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The chain's characters of a clause's metadata fixed ({lit}`chain`), at the numeral
abbreviations {lit}`nums` outside the predicate's binder: its variables', its remaining
variables' and its label's, each where an atom ({name}`fixedAtom`), and its variables' lists
lists. -/
def fixedMetaT (P : Prog) (S : Defs) (nums : Term) : Term :=
  let o := P.o
  let conj := Internal.Logic.conj o
  let f := fixedAtom P (sh 1 nums)
  let isList (n : ℕ) : Term := truth o (pc P "Datatype.isListTx"
    [pc P "Datatype.nthTx" [pc P "Datatype.elems" [v 0], leafT (numeral n)]])
  Term.lam treeTy (conj (S.allL f (metaAt P (v 0) 1)) (conj (S.allL f (metaAt P (v 0) 2))
    (conj (Term.app f (labelAtom P (v 0))) (conj (isList 1) (isList 2)))))

/-- The statement that the clauses' metadata of a list node that is a source form, each shaped as
the expansion writes it ({name}`shapeMeta`), have their characters fixed ({name}`fixedMetaT`): in
the context of the metadata v0 and the numeral abbreviations v1. -/
def metasFixedφ (P : Prog) (S : Defs) : Term :=
  Internal.Logic.imp P.o (srcAt P (v 1) (pc P "Typing.tList" [v 0]))
    (Internal.Logic.imp P.o (S.allL (shapeMeta P) (v 0)) (S.allL (fixedMetaT P S (v 1)) (v 0)))

/-- The clauses' metadata's characters fixed ({name}`metasFixedφ`): by induction on the metadata;
at a construction, the head a list of at least three elements, else its shape refuted, the tests
split at each element ({name}`andParts`); its variables' lists' elements by {name}`fixedAll`, its
label an atom whose test is its characters'. -/
def metasFixedWith (name listLemma : String) (φ : Prog → Term) (splitShape : Deducer → Deducer)
    (depth : ℕ) (P : Prog) (S : Defs) (T : Defs3) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨walkProg P, S, E, ix, (vocab3 ++ ["srcCons"]).filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size⟩
    let L := K.L
    let P := K.P
    let φ := φ P
    let Γ := [list treeTy, list treeTy]
    let nums := atPos 0
    let srcT (x : Term) (Γ : List Tree) : Term :=
      pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [sh 1 (nums Γ), v 0]), x]
    let anyFalse' : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.hypFalse h Γ Φ ψ
    -- the goal by some hypothesis, the latest first, each normalized
    let someHyp : Deducer := fun Γ Φ ψ ↦
      (dHyp Γ Φ ψ).orElse fun _ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    let d₀ ← dImpI L (dImpI L (K.solve 3)) Γ.tail []
      (Term.subst φ (Internal.instVar (nilT treeTy)))
    -- a tree's node of label rank r, the label decided, any other refuting a hypothesis; k at
    -- the position of its children
    let nodeOf (x : List Tree → Term) (r : ℕ) (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
      K.treeNode (x Γ) (normLastK K fun Γ Φ ψ ↦
        let pk := Γ.length - 1
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          if bs.map Oitavem.rank == some r then k pk
          else linkK K s!"metasFixed: the label {bs.map Oitavem.rank}" anyFalse')
          3 [] (v 1) Γ Φ ψ) Γ Φ ψ
    -- a list's split at the head, its rest empty refuting a hypothesis
    let split (xs : List Tree → Term) (k : ℕ → ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
      K.listCase treeTy (xs Γ) (linkK K "metasFixed: too few elements" anyFalse')
        (fun Γ Φ ψ ↦ k (Γ.length - 2) (Γ.length - 1) Γ Φ ψ) Γ Φ ψ
    -- the test at a list split at its head
    -- the goal by some hypothesis, both with the source forms' step unfolded, as a list's test
    -- at its elements
    let someHypU : Deducer := fun Γ Φ ψ ↦
      (someHyp Γ Φ ψ).orElse fun _ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ [.delta (T.argIdx 5)]) .full) h
          (dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta (T.argIdx 5)]) .full) dHyp) Γ Φ ψ
    let srcSplit (x : List Tree → Term) (xs : List Tree → Term) (k : Deducer) : Deducer :=
      applyThm K "andParts" (fun Γ ↦ [srcT (pc P "Typing.tList" [xs Γ]) Γ, srcT (x Γ) Γ])
        [linkK K "metasFixed: a test split" someHypU] (K.conjE k)
    -- an element's test, the source forms' step unfolded, among the hypotheses
    let srcUnfolded : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ [.delta (T.argIdx 5)]) .full) h
          (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    -- the goal's parts: the variables' lists' elements fixed, the list's node decided
    -- ({name}`fixedAll`); the label fixed where an atom; the shape's parts by the hypotheses
    let listPart (e : List Tree → Term) : Deducer :=
      nodeOf e 2 fun pk ↦ K.cutThm listLemma (fun Γ ↦ [atPos pk Γ, nums Γ]) <|
        K.impE (linkK K "metasFixed: a list's test" someHypU) fun Γ Φ ψ ↦
          K.byHyp (Φ.length - 1) Γ Φ ψ
    let labelPart (e : List Tree → Term) : Deducer := dImpI L <|
      nodeOf e 1 fun _ ↦ linkK K "metasFixed: the label's characters" srcUnfolded
    let conjs : ℕ → List Deducer → Deducer := fun n ds ↦ n.rec (fun _ _ _ ↦ none)
      fun _ rec Γ Φ ψ ↦
        match defnParts ψ with
        | some (i, _, _) =>
          if i = P.o + 1 then dConjI L rec rec Γ Φ ψ
          else ds.findSome? fun d ↦ d Γ Φ ψ
        | none => ds.findSome? fun d ↦ d Γ Φ ψ
    -- a construction: the rest v0, the head v1
    let cons : Deducer := dImpI L <| dImpI L fun Γ Φ ψ ↦
      let iShape := Φ.length - 1
      let (pm, pr) := (Γ.length - 2, Γ.length - 1)
      -- the shapes split, the head's into its parts
      (dRwHyp (evalRw K.G K.E (K.rulesEx Φ iShape) .full) iShape <| K.conjE <|
       splitShape <|
       srcSplit (atPos pm) (atPos pr) <|
       fun Γ Φ ψ ↦
        let rest : Deducer := linkK K "metasFixed: the rest" <|
          dImpE L 0 someHyp fun Γ Φ ψ ↦ dImpE L (Φ.length - 1) someHyp (fun Γ Φ ψ ↦
            K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
        (nodeOf (atPos pm) 2 fun pk ↦ split (atPos pk) fun p0 r0 ↦ split (atPos r0) fun p1 r1 ↦
          split (atPos r1) fun p2 r2 ↦
          srcSplit (atPos p0) (fun Γ ↦ consT treeTy (atPos p1 Γ)
            (consT treeTy (atPos p2 Γ) (atPos r2 Γ))) <|
          srcSplit (atPos p1) (fun Γ ↦ consT treeTy (atPos p2 Γ) (atPos r2 Γ)) <|
          srcSplit (atPos p2) (atPos r2) <|
          K.norm <| conjs depth [rest, listPart (atPos p1), listPart (atPos p2),
            labelPart (atPos p0), someHyp, K.solve 3]) Γ Φ ψ) Γ Φ ψ
    let some d₁ := linkK K "metasFixed: a construction" cons (list treeTy :: treeTy :: Γ.tail)
        [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "metasFixed: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The clauses' metadata's characters fixed ({name}`metasFixedWith`), at a case analysis's. -/
def metasFixed (P : Prog) (S : Defs) (T : Defs3) : Step :=
  metasFixedWith "metasFixed" "fixedAll" (metasFixedφ · S)
    (fun k Γ Φ ψ ↦ dConjE ⟨P.o, logicBase⟩ (Φ.length - 2)
      (fun Γ Φ ψ ↦ dConjE ⟨P.o, logicBase⟩ (Φ.length - 1) k Γ Φ ψ) Γ Φ ψ) 8 P S T

/-- The kit of the soundness at an expanded case analysis ({name}`caseCoreThm`): the statement's
variables after the case analysis's parts, its hypotheses after the parts' three, at the program of
the chain ({name}`chainProg`), the clauses' typing and the erasure's chain kept folded as well,
with the walk's rules and the chain's comparisons of lengths. -/
def caseKit (P : Prog) (S : Defs) (T : Defs3) (ix : String → ℕ) (E : Array Internal.Entry) :
    KwKit :=
  let P' := { chainProg P with
    folded := (chainProg P).folded ++ ["Typing.clausesTy", "Datatype.eraseChain"] }
  let W := kwKit P' S T ix E 4 [true, true, true, false] (expanded := true)
  { W with K := { W.K with more := (W.K.more ++ walkRules ix E ++
    lenRules.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size).eraseDups } }

/-- The chain's link of the bodies' erasures v1 to their typings v0 ({lit}`chainφ`): each body
sound at its typing ({name}`bodyφ`), in the context of the chain's statement after its two
quantifiers. -/
def chainLinkT (P : Prog) (S : Defs) (T : Defs3) : Term :=
  let o := P.o
  let headSR (xs : Term) : Term := call D.headD [srTy]
    [Term.pair (leafT bnilT) (Term.lam (list treeTy) (leafT bnilT)), xs]
  let tailSR (xs : Term) : Term := call D.tail [srTy] [xs]
  Term.app (Term.listRec (Term.lam (list srTy) (Internal.Logic.tt o))
    (Term.lam (list srTy) (Internal.Logic.conj o (bodyφ P S T 3 (v 2)
      (Term.snd (headSR (v 0)))) (Term.app (v 1) (tailSR (v 0))))) (v 1)) (v 0)

/-- The typing's map of the typings over a list of trees, as its step at a list node passes them to
the typing of lists ({lit}`Typing.synList`), at the typing environment {lit}`E`. -/
def typingMapOf (K : Kit) (T : Defs3) (Γ : List Tree) (E xs : Term) : Option Term := do
  let (z, _) ← evalRw K.G K.E (K.rules [] ++ [.delta (T.argIdx 1)]) .full Γ []
    (pc K.P "Typing.synIn" [E, nilT treeTy, pc K.P "Typing.tList" [xs]])
  let a ← (appsOf K.G (K.P.idx "Typing.synList") z).head?
  (spineArgs a)[2]?

/-- The context of {lit}`bodiesLink`: the bodies v0, the typing environment v1, the kernel's
globals' types v2, the type and numeral abbreviations v3 and v4, the definitions' names v5, the
relation's context v6 and the expansion's declarations v7. -/
def linkCtx (T : Defs3) : List Tree :=
  [list treeTy, T.envTy, list treeTy, list treeTy, list treeTy, list treeTy, Defs3.ctxTy,
    list treeTy]

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
/-- The bodies' soundness at their typings, linked as the chain reads them ({name}`chainLinkT`):
where the statement's hypotheses hold, the bodies are source forms and each is sound at expanded
forms, each body's erasure, forced, is sound at its typing; by induction on the bodies, each
body's soundness at the statement's variables, the typing's and the erasure's at the body its
antecedents. -/
def bodiesLink (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("bodiesLink", fun ix E ↦ do
    let W := caseKit P S T ix E
    let K := { W.K with more := W.K.more ++ ["srcCons"] }
    let L := K.L
    let P := K.P
    let o := P.o
    let Γ := linkCtx T
    let fm ← forcedMapOf K Γ (v 0)
    let srsT ← typingMapOf K T Γ (v 1) (v 0)
    let link := Internal.instTerm [] [srsT, fm, nilT treeTy, leafT bnilT, nilT treeTy, v 1, v 2,
      v 3, v 4, v 5, v 6, leafT bnilT] (chainLinkT P S T)
    let hs := [T.globT (v 6) (v 1) (v 5), T.numsT (v 1) (v 4), T.namesT (v 5), T.kwsT (v 4),
      Term.eq (Term.snd (v 6)) (pc P "Typing.envMs" [v 1]), T.recsT (v 6) (v 1) (v 5),
      srcAt P (v 4) (pc P "Typing.tList" [v 0]),
      S.allL (Term.lam treeTy (expandedφ P S T)) (v 0)]
    let φ := hs.foldr (Internal.Logic.imp o) link
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let intros (k : Deducer) : Deducer := (List.range hs.length).foldr (fun _ k ↦ dImpI L k) k
    let d₀ ← intros (linkK K "bodiesLink: none" (K.solve 3)) Γ.tail []
      (Term.subst φ (Internal.instVar (nilT treeTy)))
    -- a construction: the rest v0, the body v1, then the statement's variables
    let cons : Deducer := intros fun Γ₀ Φ₀ ψ₀ ↦
      let n := Φ₀.length - hs.length
      let h (i : ℕ) : ℕ := n + i
      -- positions: the declarations 0, the relation's context 1, the names 2, the numeral and type
      -- abbreviations 3 and 4, the globals' types 5, the typing environment 6, the body 7, the
      -- rest 8
      let (Rv, namesv, numsv, tysv, Gv, Ev) := (atPos 1, atPos 2, atPos 3, atPos 4, atPos 5,
        atPos 6)
      let (b, r) := (atPos 7, atPos 8)
      let srcT (x : Term) (Γ : List Tree) : Term :=
        pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [sh 1 (numsv Γ), v 0]), x]
      -- the induction hypothesis at the rest, its antecedents the hypotheses and the rest's parts
      let ih (iSr iEr : ℕ) (k : ℕ → Deducer) : Deducer :=
        ([h 0, h 1, h 2, h 3, h 4, h 5, iSr, iEr].zipIdx.foldr (fun (j, i) k Γ Φ ψ ↦
          dImpE L (if i = 0 then 0 else Φ.length - 1) (linkK K s!"bodiesLink: the rest's {i}"
            fun Γ Φ ψ ↦ (K.byHyp j Γ Φ ψ).orElse fun _ ↦ K.byNorm Γ Φ ψ) k Γ Φ ψ)
          fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ)
      -- the body's soundness at its typing: its soundness at expanded forms ({lit}`expandedφ`)
      -- at the statement's variables and the quantified context, environment and kernel's
      -- context, its antecedents the hypotheses and those introduced
      let bodyAt (iSb iEb : ℕ) : Deducer := dAllI L <| dAllI L <| dAllI L <|
        (List.range 5).foldr (fun _ k ↦ dImpI L k) fun Γ Φ ψ ↦
        let m := Φ.length - 5
        let (pcx, penv, pkc) := (Γ.length - 3, Γ.length - 2, Γ.length - 1)
        let hypOr (j : ℕ) : Deducer := fun Γ Φ ψ ↦
          (K.byHyp j Γ Φ ψ).orElse fun _ ↦ K.byNorm Γ Φ ψ
        let ante : List Deducer := [hypOr (h 0), hypOr m, hypOr (h 1), hypOr (h 2),
          hypOr iSb, K.solve 3, hypOr (m + 1), hypOr (m + 2), hypOr (m + 3),
          hypOr (h 3), hypOr (h 4), hypOr (h 5), hypOr (m + 4)]
        dAllE L K.G K.E iEb (Gv Γ) (([atPos pkc, atPos 0, Ev, atPos pcx, tysv, numsv, namesv,
            atPos penv, Rv].foldr (fun t k ↦ K.allEΓ t k)) <|
          ante.zipIdx.foldr (fun (d, i) k ↦
            K.impE (linkK K s!"bodiesLink: the body's antecedent {i}" d) k)
          (linkK K "bodiesLink: the body's conclusion" byLast)) Γ Φ ψ
      (applyThm K "andParts" (fun Γ ↦ [srcT (pc P "Typing.tList" [r Γ]) Γ, srcT (b Γ) Γ])
        [linkK K "bodiesLink: the test split" (K.byHyp (h 6))] <| K.conjE fun Γ Φ ψ ↦
      let (iSb, iSr) := (Φ.length - 2, Φ.length - 1)
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ (h 7)) .full) (h 7) (K.conjE fun Γ Φ ψ ↦
        let (iEb, iEr) := (Φ.length - 2, Φ.length - 1)
        ih iSr iEr (fun iRest ↦ K.norm <| dConjI L
          (linkK K "bodiesLink: the body" (bodyAt iSb iEb))
          (linkK K "bodiesLink: the rest" fun Γ Φ ψ ↦ (K.byHyp iRest Γ Φ ψ).orElse fun _ ↦
            -- the typings' tail rebuilt
            let reb : List Internal.NormRule :=
              [.thm (ix "rebT") [srTy], .thm (ix "rebL") [srTy, list srTy]]
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ iRest ++ reb) .full) iRest
              (dRwBy (evalRw K.G K.E (K.rules Φ ++ reb) .full) dHyp) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ) Γ₀ Φ₀ ψ₀
    let some d₁ := linkK K "bodiesLink: a construction" cons (list treeTy :: treeTy :: Γ.tail)
        [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "bodiesLink: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The bodies' erasures, forced, and their typings are equally many, as the chain's tests of their
lengths read them, neither fewer than the other: in the context of the bodies and the typing
environment; by induction on the bodies, the comparison of successors that of the lengths. -/
def lensEqual (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("lensEqual", fun ix E ↦ do
    let W := caseKit P S T ix E
    let K := { W.K with more := W.K.more ++ lenRules.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size }
    let L := K.L
    let P := K.P
    let o := P.o
    let Γ := [list treeTy, T.envTy]
    let fm ← forcedMapOf K Γ (v 0)
    let srs ← typingMapOf K T Γ (v 1) (v 0)
    let lenB (xs : Term) : Term := pc P "Datatype/Txs.length" [xs]
    let lenS (xs : Term) : Term := pc P "Typing/SRs.length" [xs]
    let notLt (a b : Term) : Term := notTest o (ltL a b)
    let φ := Internal.Logic.conj o (notLt (lenB fm) (lenS srs)) (notLt (lenS srs) (lenB fm))
    -- a false comparison's negation
    let negFalse : Deducer := fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦
      dImpI L (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    let d₀ ← linkK K "lensEqual: none" (K.norm (dConjI L negFalse negFalse)) Γ.tail []
      (Term.subst φ (Internal.instVar (nilT treeTy)))
    -- a construction: the induction hypothesis, which supplies no rule, cut in again and split;
    -- each comparison of successors that of the rest
    let cons : Deducer := fun Γ Φ ψ ↦
      dCut (Φ.getD 0 Term.star) (nd (.hyp 0)) (K.conjE fun Γ Φ ψ ↦
        let (iA, iB) := (Φ.length - 2, Φ.length - 1)
        let either : Deducer := fun Γ Φ ψ ↦
          (K.byHyp iA Γ Φ ψ).orElse fun _ ↦ (K.byHyp iB Γ Φ ψ).orElse fun _ ↦ negFalse Γ Φ ψ
        K.norm (dConjI L (linkK K "lensEqual: the first" either)
          (linkK K "lensEqual: the second" either)) Γ Φ ψ) Γ Φ ψ
    let some d₁ := linkK K "lensEqual: a construction" cons (list treeTy :: treeTy :: Γ.tail)
        [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "lensEqual: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- An element of a list of trees equal to a tree {lit}`l` by the kernel's equality, in either
order: in the context of the list and {lit}`l`; by induction on the list, at a construction the
head's equality in the goal's order decided, unequal in that order and equal in the other refuted
by the labels' equation ({lit}`eqBSound`) and reflexivity ({lit}`eqBRefl`). -/
def anyEqSymm (P : Prog) (S : Defs) : Step :=
  ("anyEqSymm", fun ix E ↦ do
    let K : Kit := ⟨caseProg P, S, E, ix, []⟩
    let L := K.L
    let P := K.P
    let o := P.o
    let Γ := [list treeTy, treeTy]
    let φ := Internal.Logic.imp o (truth o (anyT P (eqL (v 1) (v 3)) (v 0)))
      (truth o (anyT P (eqL (v 3) (v 1)) (v 0)))
    let d₀ ← dImpI L (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ.tail []
      (Term.subst φ (Internal.instVar (nilT treeTy)))
    let lb (t : Term) : Term := call D.lab [] [t]
    -- a construction: the rest v0, the head v1, the tree v2; the goal the disjunction of the
    -- head's equality and the rest's
    let cons : Deducer := dImpI L fun Γ Φ ψ ↦
      let iH := Φ.length - 1
      let (h, l, r) := (atPos (Γ.length - 2), atPos 0, atPos (Γ.length - 1))
      let headEq (Γ : List Tree) : Term := eqL (l Γ) (h Γ)
      let restAny (Γ : List Tree) : Term :=
        anyT P (eqL (sh 2 (l Γ)) (v 1)) (r Γ)
      -- equal in the hypothesis's order: the labels' equation, and the head's equality in the
      -- goal's order by reflexivity, its disjunct
      let equal : Deducer := linkK K "anyEqSymm: the head" <|
        K.cutThm "eqBSound" (fun Γ ↦ [lb (l Γ)]) <| K.allEΓ (fun Γ ↦ lb (h Γ)) <|
        K.impE (K.solve 3) <| normLastK K <|
        K.cutThm "eqBRefl" (fun Γ ↦ [lb (l Γ)]) fun Γ Φ ψ ↦
        let iR := Φ.length - 1
        K.norm (applyThm K "orLeftT" (fun Γ ↦ [restAny Γ, headEq Γ]) [K.byHyp iR]
          fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
      -- unequal: the rest's, by the induction hypothesis
      let unequal : Deducer := linkK K "anyEqSymm: the rest" fun Γ Φ ψ ↦
        dImpE L 0 (K.byHyp iH) (fun Γ Φ ψ ↦
          let iI := Φ.length - 1
          K.norm (applyThm K "orRightT" (fun Γ ↦ [restAny Γ, headEq Γ]) [K.byHyp iI]
            fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
      decideIn K (fun Γ ↦ eqL (h Γ) (l Γ)) unequal equal Γ Φ ψ
    let some d₁ := linkK K "anyEqSymm: a construction" cons (list treeTy :: treeTy :: Γ.tail)
        [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "anyEqSymm: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- Each optional type of a list present at a type {lit}`A`: present, its value {lit}`A`, as a
predicate of the list, {lit}`A` outside its binder. -/
def presentAt (P : Prog) (S : Defs) (A xs : Term) : Term :=
  let o := P.o
  S.allL (Term.lam treeTy (Internal.Logic.conj o (truth o (pc P "Prelude.isSome" [v 0]))
    (Term.eq (pc P "Prelude.get" [v 0]) (sh 1 A)))) xs

/-- The agreement of a list of optional types headed by a type present ({lit}`Typing.sameAll`)
present makes each further element present at that type ({name}`presentAt`): in the context of
the further elements and the type; by induction on them, at a construction its presence and its
value's equality with the type decided, false refuting the agreement, the equality's soundness
({lit}`equalSound`) the value's equation, the reflexivity of the type's ({lit}`equalRefl`). -/
def sameAllHead (P : Prog) (S : Defs) : Step :=
  ("sameAllHead", fun ix E ↦ do
    let K : Kit := ⟨chainProg P, S, E, ix, []⟩
    let L := K.L
    let P := K.P
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let Γ := [list treeTy, treeTy]
    let sameD := Internal.NormRule.delta (P.idx "Typing.sameAll")
    let φ := Internal.Logic.imp o (truth o (pc P "Prelude.isSome" [pc P "Typing.sameAll"
      [consT treeTy (pc P "Typing/OTy.just" [v 1]) (v 0)]]))
      (presentAt P S (v 1) (v 0))
    -- the hypothesis with the agreement unfolded, the type equal to itself
    let unfolded (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
      let A := atPos 0
      let iA := Φ.length - 1
      (K.cutThm "equalRefl" (fun Γ ↦ [A Γ]) <|
        decideIn K (fun Γ ↦ apps equalT [A Γ, A Γ]) (anyFalse K) fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ iA ++ [sameD]) .full) iA
          (fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let d₀ ← dImpI L (K.solve 3) Γ.tail [] (Term.subst φ (Internal.instVar (nilT treeTy)))
    -- a construction: the rest v0, the element v1, the type v2, at positions 2, 1 and 0
    let cons : Deducer := dImpI L <| unfolded fun iU Γ Φ ψ ↦
      let (x, A) := (atPos 1, atPos 0)
      let refute : Deducer := linkK K "sameAllHead: the agreement refuted" fun Γ Φ ψ ↦
        (K.hypFalse iU Γ Φ ψ).orElse fun _ ↦ anyFalse K Γ Φ ψ
      (decideOpt K x refute <|
        decideIn K (fun Γ ↦ apps equalT [pc P "Prelude.get" [x Γ], A Γ]) refute <|
        K.cutThm "equalSound" (fun Γ ↦ [pc P "Prelude.get" [x Γ]]) <| K.allEΓ A <|
        K.impE (linkK K "sameAllHead: the value equal" (K.solve 3)) <| normLastK K <|
        -- the induction hypothesis at the rest, its agreement the hypothesis's rest
        dImpE L 0 (linkK K "sameAllHead: the rest's agreement" fun Γ Φ ψ ↦
          dRwBy (evalRw K.G K.E (K.rules Φ ++ [sameD]) .full) (K.byHyp iU) Γ Φ ψ) <|
        fun Γ Φ ψ ↦
        let iR := Φ.length - 1
        linkK K "sameAllHead: the parts" (K.norm (dConjI L
          (dConjI L (K.solve 3) (fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦
            K.byNorm Γ Φ ψ)) (K.byHyp iR))) Γ Φ ψ) Γ Φ ψ
    let some d₁ := linkK K "sameAllHead: a construction" cons (list treeTy :: treeTy :: Γ.tail)
        [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "sameAllHead: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The agreement of a list of optional types ({lit}`Typing.sameAll`) present makes each element
present at its value ({name}`presentAt`): in the context of the list; the list split, empty
refuting the agreement; a construction, its head's presence decided, absent refuting the agreement,
present each further element by {name}`sameAllHead` at the head's value. -/
def sameAllAll (P : Prog) (S : Defs) : Step :=
  ("sameAllAll", fun ix E ↦ do
    let K : Kit := ⟨chainProg P, S, E, ix, []⟩
    let L := K.L
    let P := K.P
    let o := P.o
    let Γ := [list treeTy]
    let sameD := Internal.NormRule.delta (P.idx "Typing.sameAll")
    let same (xs : Term) : Term := pc P "Typing.sameAll" [xs]
    let a : Internal.Thm := ⟨0, Γ, [truth o (pc P "Prelude.isSome" [same (v 0)])],
      presentAt P S (pc P "Prelude.get" [same (v 0)]) (v 0)⟩
    let refute : Deducer := linkK K "sameAllAll: the agreement refuted" fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ [sameD]) .full) 0 (fun Γ Φ ψ ↦
        K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    let some d := (fun Γ Φ ψ ↦ K.listCase treeTy (atPos 0 Γ) refute (fun Γ Φ ψ ↦
        let (h, t) := (atPos (Γ.length - 2), atPos (Γ.length - 1))
        let get (u : Term) : Term := pc P "Prelude.get" [u]
        (decideOpt K h refute <|
          -- the agreement's test decided by the bits it is blocked on, false refuting it
          (fun k Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ [sameD]) .full) 0
            (fun Γ Φ ψ ↦ K.splitHyp (Φ.length - 1) k 4 Γ Φ ψ) Γ Φ ψ) <|
          K.cutThm "sameAllHead" (fun Γ ↦ [t Γ, get (h Γ)]) <|
          K.impE (linkK K "sameAllHead: the rest's agreement" fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ [sameD]) .full) 0
              (dRwBy (evalRw K.G K.E (K.rules Φ ++ [sameD]) .full) dHyp) Γ Φ ψ) fun Γ Φ ψ ↦
          let iR := Φ.length - 1
          linkK K "sameAllAll: the parts" (dRwBy (evalRw K.G K.E (K.rules Φ ++ [sameD]) .full)
            (dConjI L (dConjI L (K.solve 3) K.byNorm) (K.byHyp iR))) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "sameAllAll: not proved" fun _ ↦ none
    pure (a, d))

/-- The parts of a chain's hypotheses common to a case analysis and a structural recursion. -/
structure ClauseTools where
  /-- An else clause follows the clauses or one of their labels is the tree's. -/
  coverage : Deducer
  /-- Each clause's type is present at the common type. -/
  agreement : Deducer
  /-- A primitive's name is in no scope of a named context's names. -/
  unscoped : Term → (List Tree → Term) → Deducer
  /-- A primitive's name is no definition's. -/
  undefined : Term → Deducer

/-- The parts of a chain's hypotheses ({name}`ClauseTools`), at the typing's definition
{lit}`synDef` of the form's type, the constructors, the metadata, the bodies' typings and the
tree, whose constructor's test is the hypothesis {lit}`iMember`, the clauses' type's equation the
hypothesis {lit}`hC` and the presence of the clauses' type the hypothesis {lit}`hP`, unfolded
without the hypotheses where {lit}`bare` holds, since a decision of that presence would rewrite it
to truth. -/
def clauseTools (W : KwKit) (synDef : String) (specs metas srs t : List Tree → Term)
    (iMember hC hP : ℕ) (bare : Bool := false) : ClauseTools :=
  let K := W.K
  let L := K.L
  let P := K.P
  let T := W.T
  let ix := K.ix
  let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
  let rebSR : List Internal.NormRule :=
    [.thm (ix "rebT") [srTy], .thm (ix "rebL") [srTy, list srTy]]
  let lenT (xs : Term) : Term := pc P "Typing/Txs.length" [xs]
  let lenS (xs : Term) : Term := pc P "Typing/SRs.length" [xs]
  let labT' (Γ : List Tree) : Term := labT (t Γ)
  let ms (Γ : List Tree) : Term := pc P "Typing.envMs" [W.qv 4 Γ]
  let coveredT (Γ : List Tree) : Term :=
    allT P (anyT P (eqL (v 1) (child0 (v 3))) (sh 2 (labelsT P (metas Γ)))) (specs Γ)
  let coverage : Deducer := fun Γ Φ ψ ↦
    dRwHyp (evalRw K.G K.E (K.rulesEx Φ (W.hyp 6) ++ [.delta (P.idx synDef),
      .delta (P.idx "Typing.clausesTy")]) .full) (W.hyp 6) (fun Γ Φ ψ ↦
    let hU := Φ.length - 1
    decideIn K (fun Γ ↦ ltL (lenT (metas Γ)) (lenS (srs Γ)))
      (linkK K "clauses: no else clause" <|
        K.cutThm "covers" (fun Γ ↦ [specs Γ]) <| K.allEΓ (fun Γ ↦ labelsT P (metas Γ)) <|
        K.allEΓ labT' <|
        K.impE (linkK K "clauses: the constructors covered" <|
          decideIn K coveredT (K.hypFalse hU) (K.solve 3)) <|
        K.impE (linkK K "clauses: the member's label" <|
          K.cutThm "ctorsLabel" (fun Γ ↦ [specs Γ]) <| K.allEΓ ms <| K.allEΓ labT' <|
          K.allEΓ (fun Γ ↦ childMemberships P (ms Γ) (t Γ)) <|
          K.impE (K.byHyp iMember) byLast) <|
        linkK K "clauses: the label covered" <|
        K.cutThm "anyEqSymm" (fun Γ ↦ [labelsT P (metas Γ), labT' Γ]) <|
        K.impE (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ) fun Γ Φ ψ ↦
          byLast Γ Φ ψ)
      (K.solve 3) Γ Φ ψ) Γ Φ ψ
  -- each clause's type present at the common type: the typing's clauses' type unfolded, its
  -- covering's bits split, the agreement of the clauses' types present
  -- ({name}`sameAllAll`), its value the common type by the type's equation unfolded
  let unfoldT : List Internal.NormRule := [.delta (P.idx synDef),
    .delta (P.idx "Typing.clausesTy")]
  let agreement : Deducer := fun Γ₁ Φ₁ ψ₁ ↦ do
    -- the covering decided, an else clause's presence and the constructors' covering, false
    -- refuting the typing
    dRwHyp (evalRw K.G K.E ((if bare then K.rules [] else K.rulesEx Φ₁ hP) ++ unfoldT) .full) hP
      (fun Γ Φ ψ ↦
        let iU := Φ.length - 1
        let present : Deducer := fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ hC ++ unfoldT) .full) hC
            (fun Γ₂ Φ₂ ψ₂ ↦ do
            -- the agreement's list as the type's equation applies it
            let some tysX := (Φ₂[Φ₂.length - 1]?).bind fun e ↦
                (appsOf K.G (P.idx "Typing.sameAll") e).head?.bind fun a ↦
                  (spineArgs a).getLast?
              | dbgTrace "clauses: no agreement in the type's equation" fun _ ↦ none
            let wX (Γ : List Tree) : Term := sh (Γ.length - Γ₂.length) tysX
            applyThm K "sameAllAll" (fun Γ ↦ [wX Γ])
              [linkK K "clauses: the agreement present" fun Γ Φ ψ ↦
                dRwHyp (evalRw K.G K.E (K.rulesEx Φ iU) .full) iU (fun Γ Φ ψ ↦
                  K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ]
              (linkK K "clauses: the agreement's conclusion" fun Γ Φ ψ ↦
                (byLast Γ Φ ψ).orElse fun _ ↦
                dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1) ++ rebSR) .full)
                  (Φ.length - 1) (dRwBy (evalRw K.G K.E (K.rules Φ ++ rebSR) .full) dHyp)
                  Γ Φ ψ) Γ₂ Φ₂ ψ₂) Γ Φ ψ
        decideIn K (fun Γ ↦ ltL (lenT (metas Γ)) (lenS (srs Γ)))
          (decideIn K coveredT (linkK K "clauses: no covering" (K.hypFalse iU)) present)
          present Γ Φ ψ)
      Γ₁ Φ₁ ψ₁
  -- a primitive's name in no scope of a named context's names: there, the context gives it a
  -- type ({lit}`lookupAgreeB`), so that the typing admits it as a binder's or it is the
  -- implementation's ({lit}`Defs3.cxT`), neither of which a primitive's name is
  let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
  let unscoped (n : Term) (cx : List Tree → Term) : Deducer := dImpI L fun Γ Φ ψ ↦
    let iIn := Φ.length - 1
    (linkK K "clauses: a primitive in scope" <|
      K.cutThm "lookupAgreeB" (fun Γ ↦ [cx Γ]) <| K.allEΓ (W.qv 7) <|
      K.allEΓ (W.qv 4) <| K.allEΓ (fun _ ↦ n) <| K.impE (W.byStmt 2) <|
      K.impE (linkK K "clauses: the primitive no numeral" <| dImpI L fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1) ++
          [.delta (P.idx "Reader.numeral")]) .full) (Φ.length - 1) (dFalse L dHyp) Γ Φ ψ) <|
      K.impE (linkK K "clauses: the primitive not abbreviated" (dImpI L lastFalse)) <|
      K.impE (K.byHyp iIn) <| K.conjE fun Γ Φ ψ ↦
      let found := Φ.length - 2
      dRwHyp (evalRw K.G K.E [.delta (T.q + 7 + 2 * nFolds)] .head) (W.hyp cxHyp)
        (K.allEΓ (fun _ ↦ n) (K.impE (linkK K "clauses: the primitive given a type"
          fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ (K.byHyp found Γ Φ ψ).orElse fun _ ↦
            -- the lookup at the extended context by its equations
            let KL : Kit :=
              { K with more := K.more ++ lookupEqNames.filter (fun nm ↦ 0 < ix nm) }
            (KL.byHyp found Γ Φ ψ).orElse fun _ ↦ KL.solve 3 Γ Φ ψ)
          (linkK K "clauses: the primitive admitted" fun Γ Φ ψ ↦
            -- the primitives' names a closed list, its index unfolded
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1) ++
              [.delta (P.idx "Reader.indexOf")]) .full) (Φ.length - 1) (dFalse L dHyp)
              Γ Φ ψ))) Γ Φ ψ) Γ Φ ψ
  -- a primitive's name no definition's ({lit}`Defs3.namesT`)
  let undefined (n : Term) : Deducer := dImpI L fun Γ Φ ψ ↦
    let iIn := Φ.length - 1
    dRwHyp (evalRw K.G K.E [.delta (T.q + 4 + 2 * nFolds)] .head) (W.hyp 3)
      (K.allEΓ (fun _ ↦ n) <| K.impE (K.byHyp iIn) <|
        K.impE (linkK K "clauses: the primitive a primitive" <|
          dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta (P.idx "Reader.indexOf")]) .full)
            (K.solve 3)) lastFalse) Γ Φ ψ
  ⟨coverage, agreement, unscoped, undefined⟩

/-- The soundness at an expanded case analysis ({name}`caseCoreThm`). -/
def caseCore (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("caseCore", fun ix E ↦ do
    let W := caseKit P S T ix E
    let K := W.K
    let L := K.L
    let a := caseCoreThm (chainProg P) S T
    let P := K.P
    let equalT ← primT Kernel.Prim.equal
    -- the typing's case analysis's arguments, as the typing hypothesis's normal form applies it:
    -- the typing environment, the children, their typings and the named context; each a term of
    -- any later context
    let withSyn (k : (ℕ → List Tree → Term) → Deducer) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦ do
      let h ← Φ₀[W.hyp 6]?
      let (t, _) ← evalRw K.G K.E (K.rules Φ₀) .full Γ₀ Φ₀ h
      let some args := (appsOf K.G (P.idx "Typing.synCase") t).head?.map spineArgs
        | dbgTrace "caseCore: no typing's case analysis" fun _ ↦ none
      k (fun i Γ ↦ sh (Γ.length - Γ₀.length) (args.getD i Term.star)) Γ₀ Φ₀ ψ₀
    let typing (k : ℕ → ℕ → (List Tree → Term) → ℕ → Deducer) : Deducer := withSyn fun arg ↦
      let (Ev, rs, cx) := (arg 0, arg 2, arg 3)
      -- the typing hypothesis with the case analysis's typing unfolded, after the hypotheses;
      -- each part's absence refuting it
      fun Γ₁ Φ₁ ψ₁ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ₁ (W.hyp 6) ++
        [.delta (P.idx "Typing.synCase")]) .full) (W.hyp 6) (fun Γ Φ ψ ↦
      let hT := Φ.length - 1
      -- an optional value present, generalized, k at its variable's position
      let pres (msg : String) (opt : List Tree → Term) (k : ℕ → Deducer) : Deducer :=
        W.presentAt msg opt hT (W.hyp 6) (fun Γ Φ ψ ↦ k (Γ.length - 1) Γ Φ ψ)
          (unfolding := false)
      let refute (msg : String) : Deducer := linkK K s!"caseCore: {msg}" fun Γ Φ ψ ↦
        (K.hypFalse hT Γ Φ ψ).orElse fun _ ↦ K.hypFalse (W.hyp 6) Γ Φ ψ
      let D := atPos 0
      let mc (Γ : List Tree) : Term :=
        pc P "Typing.markerCtors" [pc P "Typing.envMs" [Ev Γ], D Γ]
      (pres "the datatype's type" (fun Γ ↦ pc P "Typing.readTy" [Ev Γ, D Γ]) fun pA ↦
      pres "the scrutinee's type" (fun Γ ↦ pc P "Typing.srAt" [rs Γ, leafT (numeral 1),
        cx Γ]) fun pB ↦
      let markers (k : Deducer) : Deducer :=
        decideIn K (fun Γ ↦ Term.fst (mc Γ)) (refute "no marker's constructors") <|
        decideIn K (fun Γ ↦ pc P "Typing.namesData" [Ev Γ, atPos pA Γ, D Γ])
          (refute "the datatype not named") k
      -- the datatype's type the scrutinee's, by the equality's soundness, decided first, so that
      -- the tests after it read the scrutinee's type; unequal, the other tests decided, the
      -- conjunction false
      decideIn K (fun Γ ↦ apps equalT [atPos pA Γ, atPos pB Γ])
        (markers (refute "the scrutinee's type another")) <|
      linkK K "caseCore: the types' equation" (
      K.cutThm "equalSound" (fun Γ ↦ [atPos pA Γ]) <| K.allEΓ (atPos pB) <|
      K.impE (linkK K "caseCore: the types equal" (K.solve 3)) <| normLastK K <|
      -- the typing's comparison then of the scrutinee's type with itself
      K.cutThm "equalRefl" (fun Γ ↦ [atPos pB Γ]) <|
      decideIn K (fun Γ ↦ apps equalT [atPos pB Γ, atPos pB Γ]) (anyFalse K) <|
      markers <|
      -- the clauses' typing as the hypothesis applies it
      fun Γ₂ Φ₂ ψ₂ ↦ do
      let (t, _) ← evalRw K.G K.E (K.rules Φ₂) .full Γ₂ Φ₂ (← Φ₂[hT]?)
      let some c := (appsOf K.G (P.idx "Typing.clausesTy") t).head?
        | dbgTrace "caseCore: no clauses' typing" fun _ ↦ none
      let c' (Γ : List Tree) : Term := sh (Γ.length - Γ₂.length) c
      -- the clauses' type generalized, its equation the last hypothesis
      (pres "the clauses' type" c' fun pC Γ Φ ψ ↦ k pB pC rs (Φ.length - 1) Γ Φ ψ) Γ₂ Φ₂ ψ₂))
        Γ Φ ψ) Γ₁ Φ₁ ψ₁
    -- a part of the case analysis a source form, its test decided, false refuting the case
    -- analysis's; its typing's form itself ({lit}`typedFixed`)
    let srcTest (Γ : List Tree) (t : Term) : Term :=
      pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [sh 1 (W.qv 7 Γ), v 0]), t]
    let typedOf (msg : String) (t : List Tree → Term) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ srcTest Γ (t Γ))
        (linkK K s!"caseCore: {msg} no source form" fun Γ Φ ψ ↦
          (K.hypFalse (W.hyp 4) Γ Φ ψ).orElse fun _ ↦
          -- the case's equation with the stage functions' steps unfolded, as the unfolding of
          -- the case analysis's leaves them
          let e := Φ.length - 1
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ e ++ W.ks.map .delta) .full) e
            (fun Γ Φ ψ ↦ K.hypFalse (W.hyp 4) Γ Φ ψ) Γ Φ ψ) <|
      K.cutThm "typedFixed" (fun Γ ↦ [t Γ]) <| K.allEΓ (W.qv 4) <| K.allEΓ (W.qv 7) <|
        K.impE (linkK K s!"caseCore: {msg} a source form" (K.solve 3)) <| normLastK K k
    -- the erasure of the metadata's list node, its elements lists ({name}`shapeMeta`), the
    -- erasure's forced map of the metadata ({name}`eraseMetas`)
    let isListP : Term := Term.lam treeTy (truth P.o (pc P "Datatype.isListTx" [v 0]))
    let metasErased (k : Deducer) : Deducer :=
      K.cutThm "allMono" (fun Γ ↦ [atPos 2 Γ]) <| K.allEΓ (fun _ ↦ shapeMeta P) <|
      K.allEΓ (fun _ ↦ isListP) <| K.impE (K.byHyp 2) <|
      K.impE (linkK K "caseCore: the metadata's shape" <| dAllI L <| dImpI L <|
        normLastK K <| K.conjE fun Γ Φ ψ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ) <|
      fun Γ Φ ψ ↦ applyThm K "eraseMetas" (fun Γ ↦ [atPos 2 Γ])
        [fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ] (fun Γ Φ ψ ↦
          -- its left side as the unfolding of the case analysis's steps leaves it, the erasure's
          -- step unfolded
          let e := Φ.length - 1
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ e ++ [.delta (T.argIdx 2)]) .full) e k Γ Φ ψ)
          Γ Φ ψ
    let negated : Deducer := dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    -- the binding of the scrutinee, the first binding the resolution's hypothesis hR reads,
    -- typed in the context: the expansion of the numeral abbreviations at it ({lit}`letNums`), in
    -- the hypothesis; then its resolution's parts ({name}`scrutLet`), k at the expanded term and
    -- body
    let binding (hR : ℕ) (k : (List Tree → Term) → (List Tree → Term) → ℕ → Deducer) :
        Deducer :=
      fun Γ₀ Φ₀ ψ₀ ↦ do
      let (t, _) ← evalRw K.G K.E (K.rules Φ₀) .full Γ₀ Φ₀ (← Φ₀[hR]?)
      let some sl := (appsOf K.G (P.idx "Datatype.sLet") t).find? fun a ↦
          (Internal.typeIn K.G 0 Γ₀ a).isSome
        | dbgTrace "caseCore: no binding" fun _ ↦ none
      let [x, a, e, b] := spineArgs sl | none
      let w (u : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) u
      let en (u : Term) (Γ : List Tree) : Term := pc P "Reader.expandNums" [W.qv 7 Γ, w u Γ]
      let scope (Γ : List Tree) : Term := scopeOf P (W.qv 7 Γ) (W.qv 5 Γ)
      (applyThm K "letNums" (fun Γ ↦ [w b Γ, w e Γ, w a Γ, w x Γ, W.qv 7 Γ]) [negated] <|
        normLastK K fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ hR) .full) hR (fun Γ Φ ψ ↦
          let hL := Φ.length - 1
          applyThm K "scrutLet" (fun Γ ↦ [en b Γ, en e Γ, scope Γ, W.qv 6 Γ, W.qv 8 Γ])
            [linkK K "caseCore: the binding resolved" (K.byHyp hL)]
            (K.conjE <| K.conjE fun Γ Φ ψ ↦
              normLastK K (k (en e) (en b) (Φ.length - 2)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
        Γ₀ Φ₀ ψ₀
    -- the kernel's typing of the resolved term, its erasure unfolded, an application of an
    -- abstraction ({lit}`letTyped`): the scrutinee's term's and the chain's typings
    let typings (eE eB : List Tree → Term) (k : (List Tree → Term) → (List Tree → Term) →
        (List Tree → Term) → ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
      let res (t sc : Term) (Γ : List Tree) : Term :=
        pc P "Reader.resolve" [W.qv 6 Γ, W.qv 8 Γ, t, sc]
      let scope (Γ : List Tree) : Term := scopeOf P (W.qv 7 Γ) (W.qv 5 Γ)
      let get (t : Term) : Term := pc P "Prelude.get" [t]
      let rE (Γ : List Tree) : Term := get (res (eE Γ) (scope Γ) Γ)
      let rB (Γ : List Tree) : Term := get (res (eB Γ)
        (consT treeTy (pc P "Reader.nameOf" [pc P "Datatype.aS" []]) (scope Γ)) Γ)
      let annK (Γ : List Tree) : Term :=
        get (pc P "Reader.readType" [W.qv 6 Γ, pc P "Datatype.aT" []])
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ (W.hyp 8) ++ [.delta (P.idx "Datatype.eraseCase")])
        .full) (W.hyp 8) (fun Γ Φ ψ ↦
        let hK := Φ.length - 1
        applyThm K "letTyped" (fun Γ ↦ [rE Γ, rB Γ, annK Γ, W.qv 2 Γ, W.qv 1 Γ])
          [linkK K "caseCore: the binding typed" (K.byHyp hK)]
          (K.conjE fun Γ Φ ψ ↦ k rE rB annK (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
        Γ Φ ψ
    -- the convergence of the binding ({lit}`letConv`), the goal's typing and erasure unfolded:
    -- the term's by the scrutinee's soundness, related at its type, the body's at any such value
    -- by k
    let converges (pB pC : ℕ) (rE rB annK : List Tree → Term) (iRes iTyped : ℕ) (k : Deducer) :
        Deducer :=
      let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
      dRwBy (fun Γ Φ t ↦ evalRw K.G K.E (K.rules Φ ++ [.delta (P.idx "Typing.synCase"),
        .delta (P.idx "Datatype.eraseCase")]) .full Γ Φ t) <|
      applyThm K "letConv" (fun Γ ↦ [W.qv 9 Γ, rE Γ, rB Γ, annK Γ,
          T.relT (W.qv 10 Γ) (atPos pB Γ), T.relT (W.qv 10 Γ) (atPos pC Γ), W.qv 10 Γ])
        [linkK K "caseCore: the scrutinee's convergence" <|
          W.soundAtWith (fun i ↦ if i = 7 then some (K.byHyp iRes)
              else if i = 8 then some (K.byHyp iTyped) else none) 0
            (fun _ ↦ none) (fun _ _ _ ↦ none) (fun _ _ _ ↦ none) byLast,
          linkK K "caseCore: the clauses' convergence" <| dAllI L <| dImpI L k]
        (linkK K "caseCore: the conclusion" byLast)
    -- the chain of the clauses ({lit}`chain`) at the member of position pt, its constructor's
    -- test the hypothesis iMember: the bodies the erasure's forced map of the bodies, their
    -- typings the case analysis's; in the named context, the environment extended by the
    -- member's quotation and the kernel's context by the annotation's type
    -- the rebuilding of lists of typings, as a tail leaves them
    let rebSR : List Internal.NormRule :=
      [.thm (ix "rebT") [srTy], .thm (ix "rebL") [srTy, list srTy]]
    let chainAt (pC hC : ℕ) (rs annK : List Tree → Term) (iResB iTypedB pt iMember : ℕ) :
        Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
      let t := atPos pt
      let specs (Γ : List Tree) : Term := Term.snd (pc P "Typing.markerCtors"
        [pc P "Typing.envMs" [W.qv 4 Γ], atPos 0 Γ])
      let bodies (Γ : List Tree) : Term := (forcedMapOf K Γ (atPos 3 Γ)).getD Term.star
      let srs (Γ : List Tree) : Term := pc P "Typing/SRs.drop" [leafT (numeral 3), rs Γ]
      let quoteT (Γ : List Tree) : Term := pc P "Eval.valQuote" [t Γ]
      -- the member's quotation related at the tree type, the scrutinee's entry's type
      let relQ : Deducer := linkK K "caseCore: the quotation related" <|
        dRwBy (fun Γ Φ u ↦ evalRw K.G K.E (K.rules Φ ++ [.thm (ix "relTTree") []]) .full Γ Φ u) <|
        fun Γ Φ ψ ↦ dExI L K.G K.E (t Γ) (K.solve 3) Γ Φ ψ
      let envOk : Deducer := applyThm K "envTCons" (fun Γ ↦ [quoteT Γ, scrutineeEntry P,
          W.qv 9 Γ, W.qv 5 Γ, W.qv 10 Γ]) [W.byStmt 1, relQ] byLast
      -- the scrutinee's label one of the clauses', or an else clause: the typing's clauses'
      -- type unfolded, the else clause's presence decided, true the first disjunct; false, the
      -- typing's covering of the constructors by the clauses' labels true, else refuting the
      -- typing, and the member's constructor's label the scrutinee's ({lit}`ctorsLabel`), one of
      -- the labels ({lit}`covers`)
      let metas := atPos 2
      let tools := clauseTools W "Typing.synCase" specs metas srs t iMember hC (W.hyp 6)
      let (coverage, agreement, unscoped, undefined) :=
        (tools.coverage, tools.agreement, tools.unscoped, tools.undefined)
      let nmS : Term := pc P "Typing.boundName" [pc P "Typing.kwScrutinee" []]
      let consS : Deducer := applyThm K "cxTCons" (fun Γ ↦ [pc P "Typing.tyT" [], nmS,
          W.qv 4 Γ, W.qv 5 Γ])
        [linkK K "caseCore: the scrutinee's name admitted" (K.solve 3), W.byStmt cxHyp] byLast
      -- the scrutinee's name's admission decided, the implementation's otherwise
      let cxOk : Deducer :=
        decideIn K (fun Γ ↦ pc P "Typing.nameOk" [W.qv 4 Γ, nmS]) consS consS
      -- the bodies and their typings equally many ({name}`lensEqual`), cut in first
      (K.cutThm "lensEqual" (fun Γ ↦ [atPos 3 Γ, W.qv 4 Γ]) <| K.conjE <| fun Γ Φ ψ ↦
      let (iA, iB) := (Φ.length - 2, Φ.length - 1)
      let lens (msg : String) : Deducer := linkK K s!"caseCore: {msg}" fun Γ Φ ψ ↦
        dRwBy (evalRw K.G K.E (K.rules Φ ++ rebSR) .full) (fun Γ Φ ψ ↦
          (K.byHyp iA Γ Φ ψ).orElse fun _ ↦ K.byHyp iB Γ Φ ψ) Γ Φ ψ
      (K.cutThm "chain" (fun Γ ↦ [atPos 2 Γ, t Γ, specs Γ, W.qv 4 Γ, W.qv 1 Γ, W.qv 6 Γ,
          W.qv 7 Γ, W.qv 8 Γ, W.qv 10 Γ, atPos pC Γ]) <|
        K.allEΓ bodies <| K.allEΓ srs <|
        K.impE (W.byStmt 10) <| K.impE (W.byStmt 9) <|
        K.impE (linkK K "caseCore: the metadata's characters" <|
          K.cutThm "metasFixed" (fun Γ ↦ [atPos 2 Γ, W.qv 7 Γ]) <|
          K.impE (linkK K "caseCore: the metadata a source form" (K.solve 3)) <|
          K.impE (linkK K "caseCore: the metadata's shape" (K.byHyp 2)) byLast) <|
        K.impE (linkK K "caseCore: the bodies' soundness" <|
          K.cutThm "bodiesLink" (fun Γ ↦ [atPos 3 Γ, W.qv 4 Γ, W.qv 1 Γ, W.qv 6 Γ, W.qv 7 Γ,
            W.qv 8 Γ, W.qv 10 Γ, W.qv 3 Γ]) <|
          ([0, 2, 3, 9, 10, 11].foldr (fun i k ↦ K.impE (W.byStmt i) k) <|
          -- the test at the case analysis's node, the source forms' step unfolded, the
          -- conjunction of the tests at the metadata's and the bodies' lists ({name}`andParts`)
          K.impE (linkK K "caseCore: the bodies source forms" <|
            applyThm K "andParts" (fun Γ ↦ [srcTest Γ (pc P "Typing.tList" [atPos 3 Γ]),
                srcTest Γ (pc P "Typing.tList" [atPos 2 Γ])])
              [fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ (W.hyp 4) ++
                  [.delta (T.argIdx 5)]) .full) (W.hyp 4)
                (dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta (T.argIdx 5)]) .full) dHyp) Γ Φ ψ] <|
            K.conjE byLast) <|
          -- the typings' list the drop of the case analysis's first three, rebuilt
          K.impE (K.byHyp 1) fun Γ Φ ψ ↦
            dRwBy (evalRw K.G K.E (K.rules Φ ++ rebSR) .full) byLast Γ Φ ψ)) <|
        K.impE (lens "the bodies' typings' number") <| K.impE (lens "the bodies' number") <|
        K.impE (linkK K "caseCore: the member's constructor" (K.byHyp iMember)) <|
        K.allEΓ (W.qv 5) <| K.allEΓ (W.qv 9) <|
        K.allEΓ (fun Γ ↦ consT treeTy (annK Γ) (W.qv 2 Γ)) <|
        K.impE (linkK K "caseCore: the coverage" coverage) <|
        K.impE (linkK K "caseCore: the types' agreement" agreement) <|
        K.impE (linkK K "caseCore: the extended environment" envOk) <|
        K.impE (linkK K "caseCore: the extended context's names" cxOk) <|
        K.impE (linkK K "caseCore: the chain resolved" (K.byHyp iResB)) <|
        K.impE (linkK K "caseCore: the chain typed" (K.byHyp iTypedB)) <|
        K.impE (linkK K "caseCore: the children primitive unscoped"
          (unscoped (childrenName P) (W.qv 5))) <|
        K.impE (linkK K "caseCore: the children primitive undefined"
          (undefined (childrenName P))) <|
        ((testPrims P).foldr (fun n k ↦
          K.impE (linkK K s!"caseCore: a test's primitive unscoped" (unscoped n (fun Γ ↦
            consT treeTy (scrutineeEntry P) (W.qv 5 Γ)))) <|
          K.impE (linkK K s!"caseCore: a test's primitive undefined" (undefined n)) k)) <|
        linkK K "caseCore: the chain's conclusion" byLast) Γ Φ ψ) Γ₀ Φ₀ ψ₀
    -- the clauses' convergence at a value related at the scrutinee's type, the innermost
    -- variable, its relation the last hypothesis: the quotation of a member of the datatype
    -- ({name}`relTDataMember`), which passes one of its constructors' tests ({lit}`memberCtors`);
    -- the chain of the clauses ({lit}`chain`) at the member
    let clauses (pB pC hC : ℕ) (rs annK : List Tree → Term) (iResB iTypedB : ℕ) : Deducer :=
      fun Γ₀ Φ₀ ψ₀ ↦
      let px := Γ₀.length - 1
      let hRel := Φ₀.length - 1
      (applyThm K "relTDataMember" (fun Γ ↦ [atPos px Γ, atPos 0 Γ, atPos pB Γ, W.qv 4 Γ,
          W.qv 10 Γ])
        [W.byStmt 10, linkK K "caseCore: the datatype named" (K.solve 3), K.byHyp hRel] <|
      K.exE <| K.conjE fun Γ Φ ψ ↦
      let pt := Γ.length - 1
      let iMem := Φ.length - 1
      applyThm K "memberCtors" (fun Γ ↦ [atPos pt Γ, atPos 0 Γ,
          pc P "Typing.envMs" [W.qv 4 Γ]]) [K.byHyp iMem]
        (fun Γ Φ ψ ↦ chainAt pC hC rs annK iResB iTypedB pt (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
        Γ₀ Φ₀ ψ₀
    -- the erasure: the case analysis's erasure unfolded in the resolution's hypothesis; the
    -- keywords it writes not abbreviated
    let erasure (pB pC : ℕ) (rs : List Tree → Term) (hC : ℕ) : Deducer :=
      metasErased fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ (W.hyp 7) ++ [.delta (P.idx "Datatype.eraseCase")])
        .full) (W.hyp 7) (fun Γ Φ ψ ↦
          let hR := Φ.length - 1
          (plainAtoms K T (walkAtoms P ++ [scrutineeName P, childrenName P] ++ testPrims P)
            (W.qv 7) (W.hyp 9)
            (lemmas := [(scrutineeName P, "scrutExcluded"), (childrenName P, "childrenExcluded"),
              (atomNameT (pc P "Datatype.aEq" []), "eqExcluded"),
              (atomNameT (pc P "Datatype.aLabel" []), "labelExcluded")]) <|
            -- the binder and the annotation their own expansions
            applyThm K "aSNums" (fun Γ ↦ [W.qv 7 Γ]) [negated] <| normLastK K <|
            applyThm K "aTNums" (fun Γ ↦ [W.qv 7 Γ]) ((walkAtoms P).map fun _ ↦ negated) <|
            normLastK K <|
            binding hR fun eE eB iRes ↦ typings eE eB fun rE rB annK iTyped ↦
            converges pB pC rE rB annK iRes iTyped
              (clauses pB pC hC rs annK (iRes - 2) (iTyped - 1))) Γ Φ ψ) Γ Φ ψ
    let some d := (List.range nQ).foldr (fun _ k ↦ dAllI L k)
        ((List.range W.nH).foldr (fun _ k ↦ dImpI L k) <|
          W.unfold (typedOf "the datatype" (atPos 0) <| typedOf "the scrutinee" (atPos 1) <|
            typedOf "the metadata" (fun Γ ↦ pc P "Typing.tList" [atPos 2 Γ]) <|
            typing erasure) 1)
        a.ctx a.hyps a.concl
      | dbgTrace "caseCore: not proved" fun _ ↦ none
    pure (a, d))

/-- A conjunction with zero is zero, its left side in normal form, so that it rewrites a
conjunction whose left test is undecided and whose right test is false. Proved by deciding the left
test. -/
def andZero (P : Prog) (S : Defs) : Step :=
  ("andZero", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let zero := leafT (numeral 0)
    let a := nfThm P (foldedRules P) [treeTy] (pc P "Prelude.and" [v 0, zero]) zero
    let some d := decideIn K (atPos 0) K.byNorm K.byNorm a.ctx a.hyps a.concl
      | dbgTrace "andZero: not proved" fun _ ↦ none
    pure (a, d))

/-- The expansion's form of a tree, the first component of its fold's value. -/
def formOf (T : Defs3) (x : Term) : Term :=
  Term.fst (Term.app (Term.snd (T.foldAt 0 [] x)) Term.star)

/-- The statement of a clause's body sound at expanded forms: in the context of the declarations
v0 and the clause v1, where the soundness holds at the clause's children, its expansion is present
and its form has two elements, it holds at the second element of the
expansion. -/
def clauseBodyThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  let o := P.o
  let ex := pc P "Datatype.expandExpr" [v 0, v 1]
  ⟨0, [list treeTy, treeTy],
    [S.allL (Term.lam treeTy (datatypeφ P S T)) (call D.children [] [v 1]),
      truth o (pc P "Prelude.isSome" [ex]),
      truth o (eqL (pc P "Prelude.length" [pc P "Datatype.elems" [formOf T (v 1)]])
        (leafT (numeral 2)))],
    Internal.instTerm [] [pc P "Datatype.nthTx" [pc P "Datatype.elems"
      [pc P "Prelude.get" [ex]], leafT (numeral 1)]] (expandedφ P S T)⟩

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
/-- A clause's body sound at expanded forms ({name}`clauseBodyThm`). -/
def clauseBody (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("clauseBody", fun ix E ↦ do
    let W₀ := kwKit P S T ix E 1 [true, true, true]
    let W : KwKit := { W₀ with K := { W₀.K with more := W₀.K.more ++ ["andZero"] } }
    let K := W.K
    let L := K.L
    let P := K.P
    let a := clauseBodyThm P S T
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    let refuteLen (msg : String) : Deducer := fun Γ Φ ψ ↦
      (K.hypFalse 2 Γ Φ ψ).orElse fun _ ↦ W.hypFalseU 2 Γ Φ ψ
    let absent (msg : String) : Deducer := linkK K s!"clauseBody: {msg} absent" fun Γ Φ ψ ↦
      (K.hypFalse 1 Γ Φ ψ).orElse fun _ ↦ W.hypFalseU 1 Γ Φ ψ
    -- the expansion of the tree at a position present, at the declarations, position 1
    let expAt (x : ℕ) (Γ : List Tree) : Term :=
      Term.app (Term.snd (Term.app (Term.snd (T.foldAt 0 [] (atPos x Γ))) Term.star)) (atPos 1 Γ)
    let present (msg : String) (opt : List Tree → Term) (k : Deducer) : Deducer :=
      decideOpt K opt (fun Γ Φ ψ ↦ ((K.hypFalse 1 Γ Φ ψ).orElse fun _ ↦ W.hypFalseU 1 Γ Φ ψ).orElse
          fun _ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ 1 ++ [.delta (T.argIdx 0)]) .full) 1
            (dFalse K.L dHyp) Γ Φ ψ)
        (W.generalize (fun Γ ↦ pc P "Prelude.get" [opt Γ]) k)
    -- the clause's elements, the pattern and the body, and the empty rest, the newest variables
    let main : Deducer := fun Γ ↦
      let (pP, pB) := (Γ.length - 4, Γ.length - 2)
      (present "the pattern's expansion" (expAt pP) <|
      present "the body's expansion" (expAt pB) <|
      -- the soundness at the pattern and at the body, after the hypotheses
      fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 (K.conjE <| K.conjE <|
      linkK K "clauseBody: the body" <|
      W.cutApply "expSound" (fun Γ ↦ [atPos pB Γ]) [anyHyp] <| K.allEΓ (atPos 1) <|
      K.impE (fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ anyHyp Γ Φ ψ) fun Γ Φ ψ ↦
      dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta (T.argIdx 0)]) .full)
        (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ
    -- a tree's node of label rank r, else k₀; k at its children's position
    let nodeOf (x : List Tree → Term) (r : ℕ) (k₀ : Deducer) (k : ℕ → Deducer) : Deducer :=
      fun Γ Φ ψ ↦ K.treeNode (x Γ) (normLastK K fun Γ Φ ψ ↦
        let pk := Γ.length - 1
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          if bs.map Oitavem.rank == some r then k pk else k₀) 3 [] (v 1) Γ Φ ψ) Γ Φ ψ
    let consK : Deducer := K.listCase treeTy (v 0) (refuteLen "one element")
      (K.listCase treeTy (v 0) main (refuteLen "more elements"))
    let nilK : Deducer := refuteLen "no elements"
    let some d := (nodeOf (atPos 0) 2 (refuteLen "the clause no list") fun pk Γ Φ ψ ↦
        K.listCase treeTy (atPos pk Γ) nilK consK Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "clauseBody: not proved" fun _ ↦ none
    pure (a, d))

/-- The list of the subterms' results ({lit}`XR`) of a list of trees v0 as the expansion's step
reads them: the argument of {lit}`xrForms` in the normal form of the elements of the form of the
list's node, the step unfolded. -/
def xrsOf (K : Kit) (T : Defs3) : Term :=
  let t := pc K.P "Datatype.elems" [formOf T (nodeT (Term.pair (numeral 2) (v 0)))]
  let fs := ((evalRw K.G K.E (K.rules [] ++ [.delta (T.argIdx 0)]) .full [list treeTy] [] t).map
    Prod.fst).getD Term.star
  match fs.label, fs.children with
  | .app, [r, _] => (match r.label, r.children with
    | .listRec, [_, _, rs] => rs
    | _, _ => Term.star)
  | _, _ => Term.star

/-- The bodies of clauses of a list of expanded clauses, each one's second element, by the
prelude's right fold, as the clauses' parts ({lit}`clauseParts`) write them. -/
def bodiesOf (P : Prog) (xs : Term) : Term :=
  foldrT treeTy (list treeTy) (Term.lam treeTy (Term.lam (list treeTy) (consT treeTy
    (pc P "Datatype.nthTx" [pc P "Datatype.elems" [v 1], leafT (numeral 1)]) (v 0))))
    (nilT treeTy) xs

/-- The statement of the bodies of clauses sound at expanded forms, in the context of the
clauses v0 and the declarations v1: where the soundness holds at each clause's children, each
clause's expansion is present ({lit}`xrFrom` at the results {lit}`rs`, those the expansion's step
reads of v0, {name}`xrsOf`) and each clause's form has two elements, it holds at the second element
of each clause's expansion. -/
def bodiesSoundφ (P : Prog) (S : Defs) (T : Defs3) (rs : Term) : Term :=
  let o := P.o
  let xo := pc P "Datatype.xrFrom" [rs, leafT (numeral 0), v 1]
  let len2 := Term.lam treeTy (truth o (eqL (pc P "Prelude.length" [pc P "Datatype.elems" [v 0]])
    (leafT (numeral 2))))
  let forms := pc P "Datatype.xrForms" [rs]
  let bodies := bodiesOf P (Term.snd xo)
  Internal.Logic.imp o (childrenφ P S T) (Internal.Logic.imp o (truth o (Term.fst xo))
    (Internal.Logic.imp o (S.allL len2 forms)
      (S.allL (Term.lam treeTy (expandedφ P S T)) bodies)))

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
/-- The bodies of clauses sound at expanded forms ({name}`bodiesSoundφ`): by induction on the
clauses; at a construction the head's expansion decided present, absent refuting the presence of
all, the head's body by {name}`clauseBody`, the rest's by the induction hypothesis. -/
def bodiesSound (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("bodiesSound", fun ix E ↦ do
    let W₀ := kwKit P S T ix E 1 [true, true, true]
    let W : KwKit := { W₀ with K := { W₀.K with more := W₀.K.more ++ ["andZero"] } }
    let K := W.K
    let L := K.L
    let P := K.P
    let rs := xrsOf K T
    let φ := bodiesSoundφ P S T rs
    let Γ := [list treeTy, list treeTy]
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    let d₀ ← linkK K "bodiesSound: none" (dImpI L <| dImpI L <| dImpI L <| K.solve 3) Γ.tail []
      (Term.subst φ (Internal.instVar (nilT treeTy)))
    -- a construction: positions the declarations 0, the head 1, the rest 2; the induction
    -- hypothesis, which supplies no rule, cut in again; the hypotheses split
    let expAt (Γ : List Tree) : Term :=
      Term.app (Term.snd (Term.app (Term.snd (T.foldAt 0 [] (atPos 1 Γ))) Term.star)) (atPos 0 Γ)
    let splitLast (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1)) .full) (Φ.length - 1) (K.conjE k) Γ Φ ψ
    let cons : Deducer := fun Γ Φ ψ ↦
      dCut (Φ.getD 0 Term.star) (nd (.hyp 0)) (dImpI L <| splitLast <|
        dImpI L <| fun Γ Φ ψ ↦
        let iAll := Φ.length - 1
        (dImpI L <| splitLast <|
        decideOpt K expAt (linkK K "bodiesSound: the head's expansion absent" fun Γ Φ ψ ↦
            K.hypFalse iAll Γ Φ ψ)
          (W.generalize (fun Γ ↦ pc P "Prelude.get" [expAt Γ]) <|
          linkK K "bodiesSound: the head's body" <|
          W.cutApply "clauseBody" (fun Γ ↦ [atPos 0 Γ, atPos 1 Γ]) [anyHyp,
            fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ anyHyp Γ Φ ψ, anyHyp] <|
          fun Γ Φ ψ ↦ dCut (Φ.getD 1 Term.star) (nd (.hyp 1)) (linkK K "bodiesSound: the rest" <|
            K.impE anyHyp <| K.impE anyHyp <| K.impE anyHyp <|
            linkK K "bodiesSound: the goal" <| K.norm <| fun Γ Φ ψ ↦
              dConjI L anyHyp anyHyp Γ Φ ψ) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ
    let some d₁ := linkK K "bodiesSound: a construction" cons (list treeTy :: treeTy :: Γ.tail)
        [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "bodiesSound: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The optional trees' type, the expansion's values'. -/
def mtxTy (P : Prog) : Tree :=
  (Internal.typeIn P.G 0 [treeTy, list treeTy] (pc P "Datatype.expandExpr" [v 1, v 0])).getD treeTy

/-- A tree's elements two, the variable of index 0. -/
def len2 (P : Prog) : Term :=
  truth P.o (eqL (pc P "Prelude.length" [pc P "Datatype.elems" [v 0]]) (leafT (numeral 2)))

/-- The hypothesis on a function {lit}`f` from a clause to its optional metadata: each clause at
which it is present has two elements and its metadata are shaped by the predicate
{lit}`shape`. -/
def metaEachAt (P : Prog) (shape f : Term) : Term :=
  let o := P.o
  let fc := Term.app (sh 1 f) (v 0)
  Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
    (truth o (pc P "Prelude.isSome" [fc]))
    (Internal.Logic.conj o (len2 P) (Internal.instTerm [] [pc P "Prelude.get" [fc]]
      (Term.app shape (v 0))))))

/-- The hypothesis of {name}`metaEachAt`, the metadata shaped as a case analysis's expansion writes
them ({name}`shapeMeta`). -/
def metaEach (P : Prog) (f : Term) : Term := metaEachAt P (shapeMeta P) f

/-- The statement of the metadata of clauses shaped: in the context of the clauses v0 and a
function v1 from a clause to its optional metadata, where each clause at which the function is
present has two elements and its metadata are shaped as the expansion writes them
({name}`shapeMeta`), and the function is present at every clause ({lit}`OTx.allJust`), each
clause has two elements and each one's metadata are so shaped. -/
def metasShapedAt (shape : Prog → Term) (P : Prog) (S : Defs) : Term :=
  let o := P.o
  let M := mtxTy P
  let ms := foldrT treeTy (list M) (Term.lam treeTy (Term.lam (list M)
    (consT M (Term.app (v 3) (v 1)) (v 0)))) (nilT M) (v 0)
  let aj := pc P "Datatype/OTx.allJust" [ms]
  Internal.Logic.imp o (metaEachAt P (shape P) (v 1)) (Internal.Logic.imp o (truth o (Term.fst aj))
    (Internal.Logic.conj o (S.allL (Term.lam treeTy (len2 P)) (v 0))
      (S.allL (shape P) (Term.snd aj))))

set_option linter.unusedVariables false in
/-- The metadata of clauses shaped ({name}`metasShapedAt`): by induction on the clauses; at a
construction the function's value at the head decided present, absent refuting the presence of
all, present its hypothesis at the head, the rest's by the induction hypothesis. -/
def metasShapedWith (name : String) (shape : Prog → Term) (P : Prog) (S : Defs) (T : Defs3) :
    Step :=
  (name, fun ix E ↦ do
    let W := kwKit P S T ix E 1 [true]
    let K := W.K
    let L := K.L
    let P := K.P
    let φ := metasShapedAt shape P S
    let Γ := [list treeTy, exp treeTy (mtxTy P)]
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    -- a conjunction of hypotheses
    let conjs : ℕ → Deducer := fun n ↦ n.rec anyHyp fun _ rec Γ Φ ψ ↦
      (anyHyp Γ Φ ψ).orElse fun _ ↦ dConjI L rec rec Γ Φ ψ
    let d₀ ← linkK K "metasShaped: none" (dImpI L <| dImpI L <| K.solve 3) Γ.tail []
      (Term.subst φ (Internal.instVar (nilT treeTy)))
    -- a construction: positions the function 0, the head 1, the rest 2
    let fAt (Γ : List Tree) : Term := Term.app (atPos 0 Γ) (atPos 1 Γ)
    -- the rest's by the induction hypothesis, the goal's conjunctions from the hypotheses
    let rest : Deducer := fun Γ Φ ψ ↦
      dCut (Φ.getD 1 Term.star) (nd (.hyp 1)) (linkK K "metasShaped: the rest" <|
        K.impE anyHyp <| K.impE anyHyp <| K.conjE <|
        linkK K "metasShaped: the goal" <| K.norm <| conjs 3) Γ Φ ψ
    -- the head's value present, the hypothesis of each, of index iEach, at the head
    let present (iEach : ℕ) : Deducer :=
      W.generalize (fun Γ ↦ pc P "Prelude.get" [fAt Γ]) fun Γ Φ ψ ↦
        dCut (Φ.getD iEach Term.star) (nd (.hyp iEach)) (K.allEΓ (atPos 1) <|
          K.impE (fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ anyHyp Γ Φ ψ) <|
          K.conjE rest) Γ Φ ψ
    let cons : Deducer := fun Γ Φ ψ ↦
      dCut (Φ.getD 0 Term.star) (nd (.hyp 0)) (dImpI L fun Γ Φ ψ ↦
        let iEach := Φ.length - 1
        dImpI L (fun Γ Φ ψ ↦
          (decideOpt K fAt (linkK K "metasShaped: the head absent" (K.hypFalse (Φ.length - 1)))
            (present iEach)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let some d₁ := linkK K "metasShaped: a construction" cons (list treeTy :: treeTy :: Γ.tail)
        [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "metasShaped: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The metadata of a case analysis's clauses shaped ({name}`metasShapedWith`). -/
def metasShaped (P : Prog) (S : Defs) (T : Defs3) : Step :=
  metasShapedWith "metasShaped" shapeMeta P S T

/-- The context of the clauses' parts ({lit}`clauseParts`), its parameters, the last first: the
entry v0, the clauses' expansions v1, the clauses v2, the datatype given v3 and the
declarations v4. -/
def partsCtx : List Tree :=
  [exp treeTy (exp treeTy treeTy), prod treeTy (list treeTy), list treeTy, treeTy, list treeTy]

/-- Whether a term mentions the definition of index k. -/
def mentions (k : ℕ) : Term → Bool := RoseTree.para fun l cs ↦
  (match l with
    | .defn j _ => j == k
    | _ => false) || cs.any (·.2)

/-- The first subterm satisfying a test, with the number of variables its binders bind around it,
from a number of them around the term. -/
def findUnder (ok : Term → Bool) : Term → ℕ → Option (Term × ℕ) := RoseTree.para fun l cs d ↦
  if ok (RoseTree.node l (cs.map Prod.fst)) then some (RoseTree.node l (cs.map Prod.fst), d) else
  match l, cs with
  | .lam _, [(_, t)] => t (d + 1)
  | .natRec, [(_, z), (_, s), (_, n)] => (z d).orElse fun _ ↦ (s (d + 1)).orElse fun _ ↦ n d
  | .listRec, [(_, z), (_, s), (_, n)] => (z d).orElse fun _ ↦ (s (d + 2)).orElse fun _ ↦ n d
  | .roseRec _, [(_, s), (_, n)] => (s (d + 1)).orElse fun _ ↦ n d
  | _, cs => cs.findSome? fun c ↦ c.2 d

/-- The element a right fold's step conses on, of a step {lit}`λ x acc. cons b acc`, the body
{lit}`b`. -/
def consBody (F : Term) : Option Term :=
  match F.label, F.children with
  | .lam _, [F₁] => (match F₁.label, F₁.children with
    | .lam _, [u] => (match u.label, u.children with
      | .arr 1 _, [p] => (match p.label, p.children with
        | .pair, [b, w] => if w == v 0 then some b else none
        | _, _ => none)
      | _, _ => none)
    | _, _ => none)
  | _, _ => none

/-- The function from a clause to its optional metadata in the clauses' parts, in their context
({name}`partsCtx`): the element the right fold of the metadata conses on, the fold's step's
body mentioning the clause's constructor ({lit}`clauseCtor`, kept folded), abstracted over the
clause, found in the normal form of the parts by the kit. -/
def metaFunAt (entry : Term) (K : Kit) : Option Term := do
  let k := K.P.idx "Datatype.clauseCtor"
  let t := pc K.P "Datatype.clauseParts" [v 4, v 3, v 2, v 1, entry]
  let (nf, _) ← evalRw K.G K.E (K.rules []) .full partsCtx [] t
  let ok (t : Term) : Bool := match t.label, t.children with
    | .pair, [F, _] => ((consBody F).map (mentions k)).getD false
    | _, _ => false
  let (p, d) ← findUnder ok nf 0
  let b ← consBody (p.children.headD Term.star)
  let free := !Term.occurs b 0 && (List.range d).all fun j ↦ !Term.occurs b (j + 2)
  if !free then none else
  pure (Term.lam treeTy (Term.subst b fun i ↦ if i = 1 then v 0 else v (i - 1 - d)))

/-- The metadata's function of the clauses' parts at the entry v0 ({name}`metaFunAt`). -/
def metaFun (K : Kit) : Option Term := metaFunAt (v 0) K

/-- The program with a clause's constructor kept folded, in which {name}`metaFun` finds the
metadata's function. -/
def ctorFolded (P : Prog) : Prog := { P with folded := P.folded ++ ["Datatype.clauseCtor"] }

set_option linter.unusedVariables false in
/-- The metadata's function of the clauses' parts ({name}`metaFun`) satisfies the hypothesis of
{name}`metasShaped` ({name}`metaEach`), in the parts' context: the presence at a clause split at
the tests it is blocked on, each false case refuting it. -/
def metaStepOk (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("metaStepOk", fun ix E ↦ do
    let W := kwKit (ctorFolded P) S T ix E 1 [true]
    let K := W.K
    let L := K.L
    let some f := metaFun K | dbgTrace "metaStepOk: no metadata function" fun _ ↦ none
    let a : Internal.Thm := ⟨0, partsCtx, [], metaEach K.P f⟩
    let some d := (dAllI L <| dImpI L <| fun Γ Φ ψ ↦
        K.splitHyp (Φ.length - 1) (linkK K "metaStepOk: a case" (K.solve 6)) 14 Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "metaStepOk: not proved" fun _ ↦ none
    pure (a, d))

/-- The reversal of a list of trees v0 onto an accumulator, the function the right fold of
{lit}`Txs.reverse` gives, found in the normal form of the reversal by the kit, the reversal its
application to the empty list. -/
def revFun (K : Kit) : Option Term := do
  let (nf, _) ← evalRw K.G K.E (K.rules []) .full [list treeTy] []
    (pc K.P "Datatype/Txs.reverse" [v 0])
  match nf.label, nf.children with
  | .app, [g, n] => if n == nilT treeTy then some g else none
  | _, _ => none

/-- The reversal of a list onto an accumulator, by {name}`revFun`'s function {lit}`g`. -/
def revT (g xs acc : Term) : Term := Term.app (Term.subst g fun i ↦ if i = 0 then xs else v i) acc

/-- The element of index i of a list of trees, the tree 0 past its end. -/
def nthT (P : Prog) (xs : Term) (i : Term) : Term := pc P "Datatype.nthTx" [xs, i]

/-- The statement of a property p of trees holding at each element of a reversal onto an
accumulator, in the context of the list v0, for every accumulator, holding at each element of
the list and of the accumulator. -/
def revAllφ (P : Prog) (S : Defs) (g p : Term) : Term :=
  let o := P.o
  Internal.Logic.all o (list treeTy) (Term.lam (list treeTy) (Internal.Logic.imp o
    (S.allL p (revT g (v 1) (v 0)))
    (Internal.Logic.conj o (S.allL p (v 1)) (S.allL p (v 0)))))

/-- The statement of the first element of a reversal onto an accumulator, in the context of the
list v0, for every accumulator: the element of the list's length's index of the list after the
accumulator's first element. -/
def lastRevφ (P : Prog) (g : Term) : Term :=
  let z := leafT (numeral 0)
  Internal.Logic.all P.o (list treeTy) (Term.lam (list treeTy) (Term.eq
    (nthT P (revT g (v 1) (v 0)) z)
    (nthT P (consT treeTy (nthT P (v 0) z) (v 1)) (pc P "Datatype/Txs.length" [v 1]))))

/-- The statement of a property p of trees holding at each element of a list v0, given that it
holds at each element but the last ({lit}`dropLast`) and at the last. -/
def dropLastAllThm (P : Prog) (S : Defs) (p : Term) : Internal.Thm :=
  let last := nthT P (v 0) (apps ((primT Kernel.Prim.sub).getD Term.star)
    [pc P "Datatype/Txs.length" [v 0], leafT (numeral 1)])
  ⟨0, [list treeTy], [S.allL p (pc P "Datatype.dropLast" [v 0]),
    Internal.instTerm [] [last] (Term.app p (v 0))], S.allL p (v 0)⟩

/-- An equation in a bitstring variable, the theorem {lit}`a`, by case analysis of its bits to a
depth, past it the remaining bits' head split as well, each case by normalization by the
vocabulary's rules with the rebuilding of doubling's fold ({lit}`rebDN`) and the double of a
successor ({lit}`dblSuccN`). -/
def byBitsSplit (K : Kit) (P : Prog) (ix : String → ℕ) (depth : ℕ) (a : Internal.Thm) :
    Option Internal.Deriv :=
  let rsH (Φ : List Term) : List Internal.NormRule :=
    [.thm (ix "rebDN") [], .thm (ix "dblSuccN") []] ++ vRules P ix ++
      (List.range Φ.length).map Internal.NormRule.hyp
  let byH : Deducer := fun Γ Φ ψ ↦
    dRwBy (evalRw K.G K.E (rsH Φ) .full)
      (dEq fun _ _ t u ↦ if t == u then some (nd .join [nd .refl, nd .refl]) else none) Γ Φ ψ
  let leaf (bs : Option (List Bool)) : Deducer := fun Γ Φ ψ ↦
    if bs.isSome then byH Γ Φ ψ
      else dBitCase K.L (ix "bitCases") (v 1) byH byH Γ Φ ψ
  dBits K.L K.G K.E (ix "listCases") (ix "bitCases") leaf depth [] (v 0) a.ctx a.hyps a.concl

/-- The numerals' regime of normalization: every definition unfolded but the successor, the sum
and the truncated difference of bitstrings, so that equations between their applications
rewrite as stated. -/
def arithR (P : Prog) : List Internal.NormRule :=
  GebTests.Prototypes.FreeTopos.Translation.baseRules ++
    [.unitVar, .deltaBelow P.o [D.succ, D.add, D.sub]]

/-- A lemma restated in the normal form of the folded program without lemmas, its successors,
sums and differences of numerals unfolded as the kernel's numerals reach them. -/
def restateU (P : Prog) (name src : String) : Step :=
  (name, fun ix E ↦ do
    let some (Internal.Entry.language a) := E[ix src]? | none
    let (l, r) ← Internal.eqParts a.concl
    let rs := foldedRules P
    let (l', dl, _) ← Internal.eval P.G E a.arity rs 4096 .full a.ctx [] l
    let (r', dr, _) ← Internal.eval P.G E a.arity rs 4096 .full a.ctx [] r
    pure (⟨a.arity, a.ctx, [], Term.eq l' r'⟩, nd (.convFrom (Term.eq l r))
      [nd .cong [dl, dr], nd (.apply (ix src) ((List.range a.arity).map x)
        ((List.range a.ctx.length).map v))]))

set_option linter.unusedVariables false in
/-- The lemmas on reversals at the property of trees of two elements ({name}`len2`): each element
of a reversal onto an accumulator ({name}`revAllφ`) and its first element ({name}`lastRevφ`) by
induction on the list, the accumulator generalized; each element of a list from each but the last
and the last ({name}`dropLastAllThm`), the list split, the reversal of its rest onto its head
split, the property at its head that at the list's last. -/
def dropLastDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let p := Term.lam treeTy (len2 P)
  let kit (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
    let W := kwKit P S T ix E 1 [true]
    let extra := (lenRules ++ ["rIterSucc", "rSuccPred"]).filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size
    { W.K with more := W.K.more ++ extra }
  -- the kit with lists' lengths kept folded
  let kitL (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
    let K := kit ix E
    { K with P := { K.P with folded := K.P.folded ++ ["Datatype/Txs.length"] } }
  let anyHyp (K : Kit) : Deducer := fun Γ Φ ψ ↦
    (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
  let conjs (K : Kit) : ℕ → Deducer := fun n ↦ n.rec (anyHyp K) fun _ rec Γ Φ ψ ↦
    ((anyHyp K) Γ Φ ψ).orElse fun _ ↦ (K.solve 1 Γ Φ ψ).orElse fun _ ↦ dConjI K.L rec rec Γ Φ ψ
  [("rebDN", fun ix E ↦ do
      -- the first component of doubling's paramorphism rebuilds the bitstring, in the
      -- vocabulary's normal form: by induction
      let rs := vRules P ix
      let some (dn, _, _) := Internal.eval P.G E 0 rs 4096 .full [bitsTy] []
          (call D.dbl [] [v 0]) | none
      let some reb := (match dn.label, dn.children with
          | .snd, [f] => some (Term.fst f)
          | _, _ => none) | none
      let φ := Term.eq reb (v 0)
      let byRs : Deducer := fun Γ Φ ψ ↦
        dRwBy (evalRw P.G E (rs ++ (List.range Φ.length).map Internal.NormRule.hyp) .full)
          (dEq fun _ _ t u ↦ if t == u then some (nd .join [nd .refl, nd .refl]) else none)
          Γ Φ ψ
      let ψ₀ := Term.subst φ (Internal.instVar (nilT bitTy))
      let d₀ ← byRs [] [] ψ₀
      let ψ₁ := Internal.listConsAt 1 bitTy φ
      let d₁ ← byRs [bitsTy, bitTy] [Internal.weakenElem φ] ψ₁
      pure (⟨0, [bitsTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁])),
    ("dblSuccN", fun ix E ↦ do
      -- the double of a successor, two before the bitstring, in the vocabulary's normal form:
      -- by induction, a construction's head bit split
      let rs := .thm (ix "rebDN") [] :: vRules P ix
      let a := nfThm P rs [bitsTy] (call D.dbl [] [call D.succ [] [v 0]])
        (consT bitTy bit1T (v 0))
      let φ := a.concl
      let byRs : Deducer := fun Γ Φ ψ ↦
        dRwBy (evalRw P.G E (rs ++ (List.range Φ.length).map Internal.NormRule.hyp) .full)
          (dEq fun _ _ t u ↦ if t == u then some (nd .join [nd .refl, nd .refl]) else none)
          Γ Φ ψ
      let d₀ ← byRs [] [] (Term.subst φ (Internal.instVar (nilT bitTy)))
      let d₁ ← dBitCase (⟨P.o, logicBase⟩ : Conn) (ix "bitCases") (v 1) byRs byRs
          [bitsTy, bitTy] [Internal.weakenElem φ] (Internal.listConsAt 1 bitTy φ)
      pure (a, nd (.listIndHyp 0 1) [d₀, d₁])),
    ("subSuccB", fun ix E ↦ do
      -- the predecessor of a successor by one, the numerals' functions folded
      let a := nfThm P (arithR P) [bitsTy] (call D.sub [] [call D.succ [] [v 0], numeral 1])
        (v 0)
      let some d := byBitsSplit (kit ix E) P ix 3 a | dbgTrace "DL subSuccB" fun _ ↦ none
      pure (a, d)),
    ("addOneB", fun ix E ↦ do
      -- the sum with one the successor, the numerals' functions folded
      let a := nfThm P (arithR P) [bitsTy] (call D.add [] [v 0, numeral 1])
        (call D.succ [] [v 0])
      let some d := byBitsSplit (kit ix E) P ix 3 a | dbgTrace "DL addOneB" fun _ ↦ none
      pure (a, d)),
    ("lenLeafR", fun ix E ↦ do
      -- a list's length the leaf of its label, in the normal form of the numerals' regime: by
      -- induction, each case by normalization
      let rs := arithR P ++ [.thm (ix "addOneB") []]
      let ln := pc P "Datatype/Txs.length" [v 0]
      let nfE (t : Term) : Term :=
        ((Internal.eval P.G E 0 rs 4096 .full [list treeTy] [] t).map fun (z, _, _) ↦ z).getD t
      let a : Internal.Thm := ⟨0, [list treeTy], [], Term.eq (nfE (leafT (call D.lab [] [ln])))
        (nfE ln)⟩
      let byRs : Deducer := dEq (fun Γ Φ t u ↦ byMode .full P.G E 0 rs Γ (rwHyps rs Φ) t u)
      let d₀ ← byRs [] [] (Term.subst a.concl (Internal.instVar (nilT treeTy)))
      let d₁ ← byRs [list treeTy, treeTy] [Internal.weakenElem a.concl]
        (Internal.listConsAt 1 treeTy a.concl)
      pure (a, nd (.listIndHyp 0 1) [d₀, d₁])),
    ("revAll", fun ix E ↦ do
      let K := kit ix E
      let L := K.L
      let g ← revFun K
      let φ := revAllφ K.P S g p
      let Γ := [list treeTy]
      let d₀ ← linkK K "revAll: none" (dAllI L <| dImpI L <| K.norm <| conjs K 2) []
        [] (Term.subst φ (Internal.instVar (nilT treeTy)))
      let cons : Deducer := fun Γ Φ ψ ↦
        dAllI L (dImpI L fun Γ Φ ψ ↦
          let h := Φ.length - 1
          dCut (Φ.getD 0 Term.star) (nd (.hyp 0)) (K.allEΓ (fun Γ ↦ consT treeTy (atPos 0 Γ)
            (atPos 2 Γ)) <| K.impE (K.byHyp h) <| K.conjE <|
            linkK K "revAll: the goal" <| K.norm <| fun Γ Φ ψ ↦
              (dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1)) .full) (Φ.length - 1)
                (K.conjE (conjs K 3)) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ
      let some d₁ := linkK K "revAll: a construction" cons [list treeTy, treeTy]
          [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
        | dbgTrace "revAll: not proved" fun _ ↦ none
      pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁])),
    ("lastRev", fun ix E ↦ do
      let K := kit ix E
      let L := K.L
      let g ← revFun K
      let φ := lastRevφ K.P g
      let Γ := [list treeTy]
      let d₀ ← linkK K "lastRev: none" (dAllI L K.byNorm) [] []
        (Term.subst φ (Internal.instVar (nilT treeTy)))
      let cons : Deducer := fun Γ Φ ψ ↦
        dAllI L (fun Γ Φ ψ ↦
          dCut (Φ.getD 0 Term.star) (nd (.hyp 0)) (K.allEΓ (fun Γ ↦ consT treeTy (atPos 0 Γ)
            (atPos 2 Γ)) <| fun Γ Φ ψ ↦
              let rs := K.rules Φ ++ ["Datatype.nthTx", "Datatype/Txs.length"].map
                fun nm ↦ Internal.NormRule.delta (K.P.idx nm)
              dRwHyp (evalRw K.G K.E rs .full) (Φ.length - 1) (dRwBy (evalRw K.G K.E rs .full)
                dHyp) Γ Φ ψ) Γ Φ ψ)
            Γ Φ ψ
      let some d₁ := linkK K "lastRev: a construction" cons [list treeTy, treeTy]
          [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
        | dbgTrace "lastRev: not proved" fun _ ↦ none
      pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁])),
    ("dropLastAll", fun ix E ↦ do
      let K₀ := kitL ix E
      let K := K₀
      let L := K.L
      let g ← revFun K
      let a := dropLastAllThm K.P S p
      -- the hypotheses' equations of a variable to another term rewrite that variable too
      let varEqs (Φ : List Term) : List Internal.NormRule :=
        (List.range Φ.length).filterMap fun i ↦ match Φ[i]?.bind Internal.eqParts with
          | some (l, r) => (match l.label with
            | .var _ => if l == r then none else some (Internal.NormRule.hyp i)
            | _ => none)
          | none => none
      let rs (Φ : List Term) : List Internal.NormRule := K.rules Φ ++ varEqs Φ ++
        ["Datatype.nthTx"].map fun nm ↦ .delta (K.P.idx nm)
      let byHypR (h : ℕ) : Deducer := fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (rs Φ) .full) h (dRwBy (evalRw K.G K.E (rs Φ) .full) dHyp) Γ Φ ψ
      let anyHypR : Deducer := fun Γ Φ ψ ↦
        (List.range Φ.length).reverse.findSome? fun h ↦ byHypR h Γ Φ ψ
      let conjsR : ℕ → Deducer := fun n ↦ n.rec anyHypR fun _ rec Γ Φ ψ ↦
        (anyHypR Γ Φ ψ).orElse fun _ ↦ (K.solve 1 Γ Φ ψ).orElse fun _ ↦
          dRwBy (evalRw K.G K.E (rs Φ) .full) (dConjI L rec rec) Γ Φ ψ
      -- positions: the list 0, its head 1, its rest 2; the reversal of the list, that of its
      -- rest onto the head
      let one (Γ : List Tree) : Term := consT treeTy (atPos 1 Γ) (nilT treeTy)
      let Y (Γ : List Tree) : Term := revT g (atPos 2 Γ) (one Γ)
      -- the property at each element of the list from that at each of the reversal
      let finish : Deducer :=
        K.cutThm "revAll" (fun Γ ↦ [atPos 2 Γ]) <| K.allEΓ one <|
          K.impE (linkK K "dropLastAll: the reversal's property" anyHypR) <| K.conjE <|
          -- the property at the head, the singleton's
          (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (rs Φ) .full) (Φ.length - 1) (K.conjE <|
            linkK K "dropLastAll: the goal" <| conjsR 3) Γ Φ ψ)
      -- the property at each element of the reversal, by its case analysis: at its head, the
      -- list's last, and at its rest
      -- the hypotheses whose normal forms equate a variable to another term, normalized after
      -- the hypotheses, so that they rewrite the variable
      let normVarEqs (k : Deducer) : Deducer := fun Γ Φ ψ ↦
        let is := (List.range Φ.length).filter fun i ↦
          match (Φ[i]?.bind fun h ↦ (evalRw K.G K.E (rs Φ) .full Γ Φ h).map Prod.fst).bind
              Internal.eqParts with
          | some (l, r) => (match l.label with
            | .var _ => l != r
            | _ => false)
          | none => false
        is.foldr (fun i k ↦ dRwHyp (evalRw K.G K.E (rs Φ) .full) i k) k Γ Φ ψ
      let allY : Deducer := fun Γ Φ ψ ↦ K.listCase treeTy (Y Γ)
        (linkK K "dropLastAll: the reversal empty" (conjsR 2))
        (normVarEqs (conjsR 3)) Γ Φ ψ
      let cons₀ : Deducer :=
        K.cutThm "revAll" (fun Γ ↦ [pc K.P "Datatype/Txs.tail" [Y Γ]]) <|
          K.allEΓ (fun _ ↦ nilT treeTy) <| K.impE (linkK K "dropLastAll: the first reversal"
            (byHypR 0)) <| K.conjE <|
          K.cutThm "lastRev" (fun Γ ↦ [atPos 2 Γ]) <| K.allEΓ one <| fun Γ Φ ψ ↦ do
            let φY := S.allL p (Y Γ)
            let dY ← allY Γ Φ φY
            dCut φY dY finish Γ Φ ψ
      -- the last element's index, the predecessor of the list's length, the rest's length,
      -- in the folded program without lemmas, the rest's length's label generalized
      let ln (x : Term) : Term := pc K.P "Datatype/Txs.length" [x]
      -- the last element's index, the predecessor of the list's length, the rest's length, as
      -- bitstrings, by rewriting in the numerals' regime
      let lastIx : Deducer := fun Γ Φ ψ ↦ do
        let e1 := Term.eq (call D.lab [] [apps ((primT Kernel.Prim.sub).getD Term.star)
          [ln (atPos 0 Γ), leafT (numeral 1)]]) (call D.lab [] [ln (atPos 2 Γ)])
        let rsA (Φ : List Term) : List Internal.NormRule := arithR K.P ++
          ["addOneB", "subSuccB", "lenLeafR"].map (fun nm ↦ .thm (K.ix nm) []) ++
          (List.range Φ.length).map Internal.NormRule.hyp
        let d1 ← dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (rsA Φ) Γ (rwHyps (rsA Φ) Φ) t u)
            Γ Φ e1
        -- the equation normalized by the rules before it, so that it rewrites normal forms
        dCut e1 d1 (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (rs Φ.dropLast) .full) (Φ.length - 1)
          cons₀ Γ Φ ψ) Γ Φ ψ
      let cons : Deducer := lastIx
      let some d := K.listCase treeTy (v 0) (K.solve 3)
          (linkK K "dropLastAll: a construction" cons) a.ctx a.hyps a.concl
        | dbgTrace "dropLastAll: not proved" fun _ ↦ none
      pure (a, d))]

/-- The arguments of an application of the definition of index k to five arguments, in order. -/
def call5 (k : ℕ) (t : Term) : Option (List Term) := do
  let some (f₄, a₅) := app2 t | none
  let some (f₃, a₄) := app2 f₄ | none
  let some (f₂, a₃) := app2 f₃ | none
  let some (f₁, a₂) := app2 f₂ | none
  let some (f₀, a₁) := app2 f₁ | none
  match f₀.label with
  | .defn j _ => if j == k then some [a₁, a₂, a₃, a₄, a₅] else none
  | _ => none
where
  /-- An application's function and argument. -/
  app2 (t : Term) : Option (Term × Term) := match t.label, t.children with
    | .app, [f, a] => some (f, a)
    | _, _ => none

/-- The clauses' parts ({lit}`clauseParts`) in their context ({name}`partsCtx`). -/
def partsT (P : Prog) : Term := pc P "Datatype.clauseParts" [v 4, v 3, v 2, v 1, v 0]

/-- The clauses' parts in their context at the entry {lit}`entry`. -/
def partsAt (P : Prog) (entry : Term) : Term :=
  pc P "Datatype.clauseParts" [v 4, v 3, v 2, v 1, entry]

/-- The statement of the clauses' parts, present, in their context ({name}`partsCtx`): the
clauses' expansions present, each clause of two elements ({name}`len2`), the metadata shaped as
the expansion writes them ({name}`shapeMeta`), and the bodies the expanded clauses' second
elements ({name}`bodiesOf`). -/
def partsOkAt (entry : Prog → Term) (ctx : List Tree) (shape : Prog → Term)
    (hyps : Prog → List Term) (P : Prog) (S : Defs) : Internal.Thm :=
  let o := P.o
  let cp := partsAt P (entry P)
  ⟨0, ctx, truth o (Term.fst cp) :: hyps P,
    Internal.Logic.conj o (truth o (Term.fst (v 1))) (Internal.Logic.conj o
      (S.allL (Term.lam treeTy (len2 P)) (v 2)) (Internal.Logic.conj o
        (S.allL (shape P) (Term.fst (Term.snd (Term.snd cp))))
        (Term.eq (Term.snd (Term.snd (Term.snd cp))) (bodiesOf P (Term.snd (v 1))))))⟩

set_option linter.unusedVariables false in
/-- The clauses' parts, present ({name}`partsOkAt`): the parts unfolded, their tests split,
false ones refuting the presence; the metadata by {lit}`metasShaped` at the metadata's function
({lit}`metaStepOk`), over the clauses but an else clause, each clause of two elements then by
{lit}`dropLastAll`. -/
def partsOkWith (name stepLemma shapedLemma : String) (entry : Prog → Term) (ctx : List Tree)
    (shape : Prog → Term) (hyps : Prog → List Term) (P : Prog) (S : Defs) (T : Defs3) : Step :=
  (name, fun ix E ↦ do
    let W := kwKit (ctorFolded P) S T ix E 1 [true]
    let K := W.K
    let L := K.L
    let P := K.P
    let a := partsOkAt entry ctx shape hyps P S
    -- the normalized copy of the parts' presence, after the given hypotheses
    let iPresent := a.hyps.length
    let some f := metaFunAt (entry P) K | dbgTrace "partsOk: no metadata function" fun _ ↦ none
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    let solveOr : Deducer := fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ anyHyp Γ Φ ψ
    -- positions: the declarations 0, the datatype given 1, the clauses 2, their expansions 3,
    -- the entry 4
    let parts (Γ : List Tree) : List Term := [atPos 4 Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
    let fAt (Γ : List Tree) : Term := Term.rename f (· + (Γ.length - ctx.length))
    -- the metadata over the clauses xs: their shapes and the clauses' two elements, the latter
    -- extended to all clauses by k
    let M := mtxTy P
    -- the metadata of the clauses xs, all present ({lit}`OTx.allJust`), as metasShaped states it
    let ajOf (xs : List Tree → Term) (Γ : List Tree) : Term :=
      pc P "Datatype/OTx.allJust" [foldrT treeTy (list M) (Term.lam treeTy (Term.lam (list M)
        (consT M (Term.app (sh 2 (fAt Γ)) (v 1)) (v 0)))) (nilT M) (xs Γ)]
    -- the metadata over the clauses xs: present, decided; their function's hypothesis, the
    -- hypothesis iEach; k at the clauses' lengths' and the shapes' hypotheses
    -- the metadata over the clauses xs: present, decided; their function's hypothesis, the
    -- hypothesis iEach; k at the clauses' lengths' and the shapes' hypotheses
    let metasOver (iEach : ℕ) (xs : List Tree → Term) (k : ℕ → ℕ → Deducer) : Deducer :=
      decideIn K (fun Γ ↦ Term.fst (ajOf xs Γ))
        (fun Γ Φ ψ ↦ (K.hypFalse iPresent Γ Φ ψ).orElse fun _ ↦ W.hypFalseU iPresent Γ Φ ψ) <|
      K.cutThm shapedLemma (fun Γ ↦ [xs Γ, fAt Γ]) <|
        K.impE (linkK K "partsOk: the metadata's function" (K.byHyp iEach)) <|
        K.impE (linkK K "partsOk: the metadata present" (K.solve 3)) <| K.conjE <|
        fun Γ Φ ψ ↦ k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ
    let goal (lens : ℕ → Deducer) (iLen iShape : ℕ) : Deducer :=
      linkK K "partsOk: the goal" <|
        dConjI L (linkK K "partsOk: the expansions" (K.solve 3)) <|
        dConjI L (linkK K "partsOk: the clauses' lengths" (lens iLen)) <|
        dConjI L (linkK K "partsOk: the shapes" (K.byHyp iShape))
          (linkK K "partsOk: the bodies" K.byNorm)
    -- the clauses' tests as the parts read them: the last clause, whether it is an else
    -- clause, of a list, two elements and the keyword else at its head
    let lenT (x : Term) : Term := pc P "Datatype/Txs.length" [x]
    let lastC (Γ : List Tree) : Term := pc P "Datatype.nthTx" [atPos 2 Γ,
      apps ((primT Kernel.Prim.sub).getD Term.star) [lenT (atPos 2 Γ), leafT (numeral 1)]]
    let isList (Γ : List Tree) : Term := pc P "Datatype.isListTx" [lastC Γ]
    let two (Γ : List Tree) : Term :=
      eqL (lenT (pc P "Datatype.elems" [lastC Γ])) (leafT (numeral 2))
    let named (Γ : List Tree) : Term := pc P "Datatype.namedTx"
      [pc P "Datatype.nthTx" [pc P "Datatype.elems" [lastC Γ], leafT (numeral 0)],
        pc P "Datatype.kwElse" []]
    let andT (a b : Term) : Term := pc P "Prelude.and" [a, b]
    let hasElse (Γ : List Tree) : Term := andT (isList Γ) (andT (two Γ) (named Γ))
    -- the else clause: its two elements from the test, split by andParts twice
    let withElse (iEach : ℕ) : Deducer :=
      applyThm K "andParts" (fun Γ ↦ [andT (two Γ) (named Γ), isList Γ]) [K.solve 3] <|
      K.conjE <| fun Γ Φ ψ ↦
      applyThm K "andParts" (fun Γ ↦ [named Γ, two Γ]) [K.byHyp (Φ.length - 1)] (K.conjE <|
      metasOver iEach (fun Γ ↦ pc P "Datatype.dropLast" [atPos 2 Γ]) <| goal fun iLen ↦
        applyThm K "dropLastAll" (fun Γ ↦ [atPos 2 Γ])
          [K.byHyp iLen, linkK K "partsOk: the last clause" fun Γ Φ ψ ↦
            (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ]
          fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    let withoutElse (iEach : ℕ) : Deducer := metasOver iEach (atPos 2) (goal K.byHyp)
    let refute : Deducer := fun Γ Φ ψ ↦
      (K.hypFalse iPresent Γ Φ ψ).orElse fun _ ↦ W.hypFalseU iPresent Γ Φ ψ
    -- the parts' tests decided: the clauses' expansions present, the clauses some, an else
    -- clause or not
    let leaf : Deducer :=
      decideIn K (fun Γ ↦ Term.fst (atPos 3 Γ)) (linkK K "partsOk: expansions absent" refute) <|
      decideIn K (fun Γ ↦ ltL (leafT (numeral 0)) (lenT (atPos 2 Γ)))
        (linkK K "partsOk: no clauses" refute) <|
      applyThm K stepLemma parts ((List.range (hyps P).length).map fun i ↦ K.byHyp (i + 1))
        fun Γ Φ ψ ↦
        let iEach := Φ.length - 1
        decideIn K hasElse (withoutElse iEach) (withElse iEach) Γ Φ ψ
    let some d := (dRwHyp (evalRw K.G K.E (K.rulesEx [] 0 ++
        [.delta (P.idx "Datatype.clauseParts")]) .full) 0 leaf) a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The clauses' parts of a case analysis, present ({name}`partsOkWith`). -/
def partsOk (P : Prog) (S : Defs) (T : Defs3) : Step :=
  partsOkWith "partsOk" "metaStepOk" "metasShaped" (fun _ ↦ v 0) partsCtx shapeMeta (fun _ ↦ [])
    P S T

/-- The first component of the list case's fold over a list of the subterms' results ({lit}`XR`),
its rebuilding, is the list: the fold as the normal form of the list's tail ({lit}`XRs.tail`) by the
kit writes it, in the context of the list; by induction. -/
def rebXR (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("rebXR", fun ix E ↦ do
    let W := kwKit P S T ix E 1 [true]
    let K := W.K
    let some elemTy := Internal.typeIn K.G 0 [treeTy]
      (Term.app (Term.snd (T.foldAt 0 [] (v 0))) Term.star) | none
    let lt := list elemTy
    let (tl, _) ← evalRw K.G K.E (K.rules []) .full [lt] [] (pc K.P "Datatype/XRs.tail" [v 0])
    let some f := (match tl.label, tl.children with
        | .snd, [f] => some f
        | _, _ => none) | none
    let φ := Term.eq (Term.fst f) (v 0)
    let byRs : Deducer := fun Γ Φ ψ ↦
      dRwBy (evalRw K.G K.E (K.rules [] ++ (List.range Φ.length).map Internal.NormRule.hyp) .full)
        (dEq fun _ _ t u ↦ if t == u then some (nd .join [nd .refl, nd .refl]) else none) Γ Φ ψ
    let d₀ ← byRs [] [] (Term.subst φ (Internal.instVar (nilT elemTy)))
    let d₁ ← byRs [lt, elemTy] [Internal.weakenElem φ] (Internal.listConsAt 1 elemTy φ)
    pure (⟨0, [lt], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The statement of a form at fewer elements after the keyword {lit}`kw` than its expansion
reads, which the expansion reads as an application of the keyword's atom: the statement introduced;
the atom's expanded form sound (atomCase, expSound); each element, at the positions {lit}`elems`,
its expansion decided present and its expanded form sound; the application's soundness at expanded
forms (appCore) at them, instantiated at the statement's variables, its hypotheses the statement's,
its keywords' tests by normalization. In the kit {lit}`K` and, with the form's expansion unfolded,
{lit}`Ku`. -/
def srcShort (Pc : Prog) (kw : String) (K Ku : Kit) (S : Defs) (T : Defs3) (msg : String)
    (elems : List ℕ) : Deducer :=
  let (L, P, ix, E) := (K.L, K.P, K.ix, K.E)
  let anyHyp : Deducer := fun Γ Φ ψ ↦
    (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
  let last : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
  let splitHypAt (h : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
    dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h (K.conjE k) Γ Φ ψ
  let unfold := ((List.range nFolds).map T.argIdx ++
    [P.idx "Typing.synList", P.idx "Reader.resolveList"]).map Internal.NormRule.delta
  let kwA := kwAtom P kw
  let kwChars : Term := match kwA.children with
    | [p] => (match p.children with
      | [_, cs] => cs
      | _ => Term.star)
    | _ => Term.star
  -- a goal from a hypothesis, both normalized with the folds' steps unfolded
  let byUnfold (h : ℕ) : Deducer := fun Γ Φ ψ ↦
    dRwHyp (evalRw K.G K.E (Ku.rulesEx Φ h ++ unfold) .full) h
      (dRwBy (evalRw K.G K.E (Ku.rules Φ ++ unfold) .full) dHyp) Γ Φ ψ
  fun Γ₀ Φ₀ ψ₀ ↦
    let W : KwKit := { kwKit Pc S T ix E Γ₀.length (List.replicate Φ₀.length true) kw with K := K }
    -- the rest of the elements' soundness, a conjunction of hypotheses ending in truth
    let restElems (n : ℕ) : Deducer := n.rec (fun _ _ _ ↦ none) fun _ rec Γ Φ ψ ↦
      (K.solve 3 Γ Φ ψ).orElse fun _ ↦ dConjI L anyHyp rec Γ Φ ψ
    let core (rest : List Tree → Term) : Deducer :=
      K.cutThm "atomCase" (fun _ ↦ [kwChars]) <|
      W.cutApply "expSound" (fun _ ↦ [kwA]) [last] <| K.allEΓ (W.qv 3) <|
      K.impE (linkK K s!"caseSrc: {msg}: the keyword's expansion" fun Γ Φ ψ ↦
        dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold) .full) (K.solve 3) Γ Φ ψ) <|
      fun Γ Φ ψ ↦
      let iHead := Φ.length - 1
      (applyThm K "appCore" (fun Γ ↦ [rest Γ, kwA])
        [linkK K s!"caseSrc: {msg}: the keyword" fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ iHead ++ unfold) .full) iHead
            (dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold) .full) dHyp) Γ Φ ψ,
          linkK K s!"caseSrc: {msg}: the elements" (K.norm fun Γ Φ ψ ↦
            (K.solve 3 Γ Φ ψ).orElse fun _ ↦
            dConjI L (fun Γ Φ ψ ↦ (K.byHyp (iHead - 4) Γ Φ ψ).orElse fun _ ↦
              anyHyp Γ Φ ψ) (restElems elems.length) Γ Φ ψ)] <|
      linkK K s!"caseSrc: {msg}: the instance" fun Γ Φ ψ ↦
        dAllE L K.G K.E (Φ.length - 1) (W.qv 1 Γ) (((List.range (nQ - 1)).foldr
          (fun j k ↦ K.allEΓ (W.qv (j + 2)) k) <|
          (List.range W.nH).foldr (fun i k ↦ K.impE (linkK K s!"caseSrc: {msg}: hypothesis {i}"
            fun Γ Φ ψ ↦ (byStatement Ku (W.hyp i) Γ Φ ψ).orElse fun _ ↦
              byUnfold (W.hyp i) Γ Φ ψ) k) <|
          (List.range (headFree P T).length).foldr (fun j k ↦
            K.impE (linkK K s!"caseSrc: {msg}: keyword test {j}" fun Γ Φ ψ ↦
              dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold) .full) (K.solve 3) Γ Φ ψ) k) <|
          fun Γ Φ ψ ↦ (Ku.byHyp (Φ.length - 1) Γ Φ ψ).orElse fun _ ↦
            byUnfold (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ
    -- the keyword's name abbreviated or not, as appAtom decides it: abbreviated, the
    -- abbreviation a numeral's atom, by the coherence of the abbreviations, which no reader's
    -- keyword names
    let nm : Term := nameOfChars P kwChars
    let abbrevSplit (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [nm, W.qv 7 Γ]]) k
        (linkK K s!"caseSrc: {msg}: the abbreviation" <|
        dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) (W.hyp 2) fun Γ Φ ψ ↦
        dAllE L K.G K.E (Φ.length - 1) nm (K.conjE fun Γ Φ ψ ↦
          let (n₁, n₂) := (Φ.length - 2, Φ.length - 1)
          dImpE L n₂ (K.solve 3) (fun Γ Φ ψ ↦
            dImpE L n₁ (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) (K.exE <| K.conjE
              fun Γ Φ ψ ↦
              let iNum := Φ.length - 1
              let dsPos := Γ.length - 1
              (readerKeywords.foldr (fun kw k ↦ W.cutApply s!"numeralUnnamed/{kw}"
                  (fun Γ ↦ [atPos dsPos Γ]) [K.byHyp iNum] k) k) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
    -- each element's expansion decided present and its expanded form sound, the expansions'
    -- positions collected; then the application at them
    let elements : List ℕ → List ℕ → ℕ → Deducer := fun ps ↦
      ps.rec (fun acc _ ↦ core fun Γ ↦
          acc.foldl (fun t p ↦ consT treeTy (atPos p Γ) t) (nilT treeTy))
        (fun p _ rec acc hR ↦
          -- the statement at the first of the rest, of index hR, and the rest's
          splitHypAt hR fun Γ Φ ψ ↦
          let iR := Φ.length - 1
          (W.presentAt s!"{msg}: an element's expansion" (fun Γ ↦
              pc P "Datatype.expandExpr" [W.qv 3 Γ, atPos p Γ]) (W.hyp 5) (W.hyp 5)
            (W.cutApply "expSound" (fun Γ ↦ [atPos p Γ]) [linkK K s!"{msg}: soundness" anyHyp] <|
              K.allEΓ (W.qv 3) <| K.impE (K.solve 3) fun Γ Φ ψ ↦
                rec ((Γ.length - 1) :: acc) iR Γ Φ ψ)) Γ Φ ψ)
    ((List.range nQ).foldr (fun _ k ↦ dAllI L k) <| (List.range W.nH).foldr
      (fun _ k ↦ dImpI L k) <| abbrevSplit <|
      elements elems [] 0) Γ₀ Φ₀ ψ₀

/-- The statement of the soundness at a case analysis at source forms: in the context of the
elements after the keyword, given the soundness at each and at each one's children, the soundness at
the list the keyword heads ({lit}`headedφ` without its quantifier). -/
def caseSrcThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  ⟨0, [list treeTy], [S.allL (Term.lam treeTy (datatypeφ P S T)) (v 0), childrenφ P S T],
    Internal.instTerm [] [listOf (kwAtom P "Datatype.kwCase") (v 0)] (datatypeφ P S T)⟩

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
/-- The soundness at a case analysis at source forms ({name}`caseSrcThm`). -/
def caseSrc (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("caseSrc", fun ix E ↦ do
    let Pc : Prog := { chainProg P with
      folded := (chainProg P).folded ++ ["Datatype.clauseParts"] }
    let W₀ := kwKit Pc S T ix E 1 [true, true] "Datatype.kwCase"
    let extra := (lenRules ++ ["ltSucc2", "rebXR"]).filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size
    let W : KwKit :=
      { W₀ with K := { W₀.K with more := (W₀.K.more ++ walkRules ix E ++ extra).eraseDups } }
    let K := W.K
    let L := K.L
    let P := K.P
    -- the kit with the expansion of case analyses unfolded, in which the statement's
    -- expansion and the expanded case analysis's agree
    let Ku : Kit := { K with P := { K.P with
      folded := K.P.folded.filter (· != "Datatype.expandCase") } }
    let a := caseSrcThm P S T
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    let last : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let splitHypAt (h : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h (K.conjE k) Γ Φ ψ
    -- the main case, the elements the scrutinee 1, a clause 3 and the further clauses 4, the
    -- scrutinee's expansion the last variable, the expansion's presence the hypothesis hE: the
    -- clauses' parts q decided present; their facts (partsOk); the scrutinee sound at expanded
    -- forms (expSound), the bodies (bodiesSound); caseCore at the parts, instantiated at the
    -- statement's variables, its hypotheses the statement's
    let main (W : KwKit) (hE : ℕ) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦ do
      let pS := Γ₀.length - 1
      let (t, _) ← evalRw K.G K.E (K.rules Φ₀) .full Γ₀ Φ₀ (← Φ₀[hE]?)
      let some (q₀, 0) := findUnder (fun t ↦ (call5 (P.idx "Datatype.clauseParts") t).isSome)
          t 0 | none
      let args₀ ← call5 (P.idx "Datatype.clauseParts") q₀
      let up (t : Term) (Γ : List Tree) : Term := Term.rename t (· + (Γ.length - Γ₀.length))
      let q (Γ : List Tree) : Term := up q₀ Γ
      let rest (Γ : List Tree) : Term := consT treeTy (atPos 3 Γ) (atPos 4 Γ)
      let caseCoreAt : Deducer := fun Γ Φ ψ ↦
        -- after partsOk's conjunctions (shapes, bodies' equation), expSound's three steps and
        -- bodiesSound's four
        let (iExp, iBodies, iShape) := (Φ.length - 5, Φ.length - 1, Φ.length - 9)
        (applyThm K "caseCore" (fun Γ ↦ [Term.snd (Term.snd (Term.snd (q Γ))),
            Term.fst (Term.snd (Term.snd (q Γ))), atPos pS Γ, Term.fst (Term.snd (q Γ))])
          [linkK K "caseSrc: the scrutinee" (K.byHyp iExp),
            linkK K "caseSrc: the bodies" (K.byHyp iBodies),
            linkK K "caseSrc: the shapes" (K.byHyp iShape)] <|
        linkK K "caseSrc: the instance" fun Γ Φ ψ ↦
          dAllE L K.G K.E (Φ.length - 1) (W.qv 1 Γ) (((List.range (nQ - 1)).foldr
            (fun j k ↦ K.allEΓ (W.qv (j + 2)) k) <|
            (List.range W.nH).foldr (fun i k ↦ K.impE (linkK K s!"caseSrc: hypothesis {i}"
              (byStatement Ku (W.hyp i))) k) fun Γ Φ ψ ↦ Ku.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ)
          Γ Φ ψ
      (splitHypAt 0 <| splitHypAt 1 <|
        decideIn K (fun Γ ↦ Term.fst (q Γ))
          (linkK K "caseSrc: the parts absent" fun Γ Φ ψ ↦
            (K.hypFalse hE Γ Φ ψ).orElse fun _ ↦ W.hypFalseU hE Γ Φ ψ) <|
        applyThm K "partsOk" (fun Γ ↦ (args₀.map (up · Γ)).reverse)
          [linkK K "caseSrc: the parts present" (K.solve 3)] <|
        K.conjE <| K.conjE <| K.conjE <|
        -- the scrutinee's expanded form sound
        W.cutApply "expSound" (fun Γ ↦ [atPos 1 Γ])
          [linkK K "caseSrc: the scrutinee's soundness" anyHyp] <|
        K.allEΓ (W.qv 3) <| K.impE (linkK K "caseSrc: the scrutinee present" (K.solve 3)) <|
        -- the bodies sound
        K.cutThm "bodiesSound" (fun Γ ↦ [rest Γ, W.qv 3 Γ]) <|
        K.impE (linkK K "caseSrc: the clauses' children" anyHyp) <|
        K.impE (linkK K "caseSrc: the clauses' expansions" anyHyp) <|
        K.impE (linkK K "caseSrc: the clauses' lengths" anyHyp) caseCoreAt) Γ₀ Φ₀ ψ₀
    -- the statement at a list of at least two elements after the keyword, its kit at the
    -- context reached: the quantifiers and hypotheses introduced; the steps unfolded; the
    -- expansion of case analyses unfolded in the expansion's presence; the scrutinee's
    -- expansion decided present
    let mk (n h : ℕ) : KwKit :=
      { kwKit Pc S T ix E n (List.replicate h true) "Datatype.kwCase" with K := K }
    let mainBranch : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let W := mk Γ₀.length Φ₀.length
      ((List.range nQ).foldr (fun _ k ↦ dAllI L k) <| (List.range W.nH).foldr
        (fun _ k ↦ dImpI L k) <|
        W.unfold (fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ (W.hyp 5) ++
            [.delta (P.idx "Datatype.expandCase")]) .full) (W.hyp 5) (fun Γ Φ ψ ↦
            let hE := Φ.length - 1
            (W.presentAt "the scrutinee's expansion" (fun Γ ↦
                pc P "Datatype.expandExpr" [W.qv 3 Γ, atPos 1 Γ]) hE (W.hyp 5)
              (main W hE) (unfolding := false)) Γ Φ ψ) Γ Φ ψ) 1) Γ₀ Φ₀ ψ₀
    let refute (msg : String) (ps : List ℕ) : Deducer :=
      srcShort Pc "Datatype.kwCase" K Ku S T msg ps
    let some d := K.listCase treeTy (v 0) (refute "no elements" [])
        (K.listCase treeTy (v 0) (refute "one element" [1]) mainBranch) a.ctx a.hyps a.concl
      | dbgTrace "caseSrc: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at every list headed by the keyword of case analyses ({lit}`headedφ`), from
that at source forms ({name}`caseSrc`): its quantifier and hypotheses introduced. -/
def caseHeaded (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("caseHeaded", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let φ := headedφ P S T "Datatype.kwCase"
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    let some d := (dAllI K.L <| dImpI K.L <| dImpI K.L <|
        applyThm K "caseSrc" (fun Γ ↦ [atPos 0 Γ]) [anyHyp, anyHyp] fun Γ Φ ψ ↦
          K.byHyp (Φ.length - 1) Γ Φ ψ) [] [] φ
      | dbgTrace "caseHeaded: not proved" fun _ ↦ none
    pure (⟨0, [], [], φ⟩, d))

/-- The development of the soundness at a case analysis. -/
def caseSoundDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [scrutNums P S T, scrutLet P S, relTDataMember P S T, andParts P S, fixedAll P S T,
    metasFixed P S T, bodiesLink P S T, lensEqual P S T, anyEqSymm P S, sameAllHead P S,
    sameAllAll P S, caseCore P S T, andZero P S, clauseBody P S T, bodiesSound P S T,
    metasShaped P S T, metaStepOk P S T] ++ dropLastDev P S T ++
    [partsOk P S T, rebXR P S T, caseSrc P S T, caseHeaded P S T]

/-- The soundness at a case analysis, after the clauses' development. -/
def caseSoundCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := caseNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (caseDev P S T).map (·.1) ++ (clausesDev P S T).map (·.1))
    "datatype-case-sound" (caseSoundDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
