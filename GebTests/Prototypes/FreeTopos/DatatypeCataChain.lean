/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeCataClauses
public meta import GebTests.Prototypes.FreeTopos.DatatypeCataClauses -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at the chain of a structural recursion's clauses

The soundness of the datatype language's stage-1 compiler at the chain of tests of the clauses of a
structural recursion, the case analysis's chain ({lit}`chainWith`) at the recursion's specification.

## Main definitions

* {lit}`cataChainCertificates` — the development, stored as the certificate
  {lit}`datatype-cata-chain`.

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

/-- An entry has no third element, as the expansion writes it, as a predicate of an entry. -/
def shapeEntry (P : Prog) : Term :=
  Term.lam treeTy (notTest P.o (pc P "Prelude.isSome"
    [pc P "Prelude.nth" [pc P "Datatype.elems" [v 0], leafT (numeral 2)]]))

/-- The erasure fixes an entry, its variable admitted as a binder, its flag a numeral's atom and
without a third element: the entry's node a list's, of the two elements, else a hypothesis refuted;
the variable's node an atom's, whose name, admitted, is none of the keywords the erasure's step
rewrites a list headed by; the flag's atom by its equation ({lit}`equalSound`). In the context of
the entry and the typing environment. -/
def eraseEntry (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("eraseEntry", fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, walkRules ix E ++ ["nthTwo3"]⟩
    let L := K.L
    let Γ := [treeTy, T.envTy]
    let step ← eraseStepIdx K
    let equalT ← primT Kernel.Prim.equal
    let a : Internal.Thm := ⟨0, Γ, [Term.app (binderEntry P (v 1)) (v 0),
      Term.app (flagEntry P) (v 0), Term.app (shapeEntry P) (v 0)],
      Term.eq (pc P "Datatype.eraseExpr" [v 0]) (v 0)⟩
    let byS : Deducer := fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ [.delta step]) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let refute (msg : String) (h : ℕ) : Deducer := linkK K s!"eraseEntry: {msg}" (K.hypFalse h)
    let (hB, hF, hS) := (0, 1, 2)
    let named (kw : String) (x : List Tree → Term) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Datatype.namedTx" [x Γ, pc P kw []]) k
        (linkK K s!"eraseEntry: the variable named by {kw}" fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ hB ++
            [.delta (P.idx "Typing.binderName"), .delta (P.idx "Typing.nameOk")]) .full) hB
            (dFalse L dHyp) Γ Φ ψ)
    let (a0, a1) := (pc P "Datatype.numAtom" [leafT bnilT], pc P "Datatype.numAtom"
      [leafT (numeral 1)])
    let eqAt (f : List Tree → Term) (at' : Term) : Deducer :=
      linkK K "eraseEntry: the flag" <|
      K.cutThm "equalSound" (fun Γ ↦ [f Γ]) <| K.allEΓ (fun _ ↦ at') <|
      K.impE (K.solve 3) (linkK K "eraseEntry: the sides" byS)
    let flagged (f : List Tree → Term) : Deducer :=
      decideIn K (fun Γ ↦ apps equalT [f Γ, a1])
        (decideIn K (fun Γ ↦ apps equalT [f Γ, a0]) (refute "the flag neither" hF) (eqAt f a0))
        (eqAt f a1)
    let some d := (K.treeNode (v 0) (normLastK K fun Γ Φ ψ ↦
        let pK := Γ.length - 1
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          if bs.map Oitavem.rank == some 2 then fun Γ Φ ψ ↦
            K.listCase treeTy (atPos pK Γ) (refute "no variable" hB) (fun Γ Φ ψ ↦
              let (pX, pR) := (Γ.length - 2, Γ.length - 1)
              K.listCase treeTy (atPos pR Γ) (refute "no flag" hF) (fun Γ Φ ψ ↦
                let (pF, pR') := (Γ.length - 2, Γ.length - 1)
                K.listCase treeTy (atPos pR' Γ)
                  (fun Γ Φ ψ ↦ K.treeNode (atPos pX Γ) (normLastK K fun Γ Φ ψ ↦
                    dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
                      if bs.map Oitavem.rank == some 1 then
                        named "Typing.kwRep" (atPos pX) <| named "Typing.kwDecode" (atPos pX) <|
                        named "Typing.kwDatum" (atPos pX) <| flagged (atPos pF)
                      else refute s!"the variable's label {bs.map Oitavem.rank}" hB)
                      3 [] (v 1) Γ Φ ψ) Γ Φ ψ)
                  (linkK K "eraseEntry: a third element" <| normHyps K [hS] <| fun Γ Φ ψ ↦
                    dImpE L (Φ.length - 1) (K.solve 3)
                      (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
                Γ Φ ψ) Γ Φ ψ
          else refute s!"the label {bs.map Oitavem.rank}" hB)
          3 [] (v 1) Γ Φ ψ)) a.ctx a.hyps a.concl
      | dbgTrace "eraseEntry: not proved" fun _ ↦ none
    pure (a, d))

/-- The erasure's forced map over a list of entries each fixed ({name}`eraseEntry`) is the list: by
induction. In the context of the list and the typing environment. -/
def eraseEntriesMap (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("eraseEntriesMap", fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let o := P.o
    let imp := Internal.Logic.imp o
    let Γ := [list treeTy, T.envTy]
    let some fm := forcedMapOf K Γ (v 0) | dbgTrace "eraseEntriesMap: no map" fun _ ↦ none
    let step ← eraseStepIdx K
    let φ := imp (S.allL (binderEntry P (v 1)) (v 0)) <| imp (S.allL (flagEntry P) (v 0)) <|
      imp (S.allL (shapeEntry P) (v 0)) (Term.eq fm (v 0))
    let byS : Deducer := fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ [.delta step]) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let d₀ ← dImpI L (dImpI L (dImpI L (linkK K "eraseEntriesMap: empty" byS))) [T.envTy] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the environment, the head, the rest; hypotheses: the induction hypothesis, then
    -- the three lists'; each split at its head
    let splits (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
      let (i₁, i₂, i₃) := (Φ.length - 3, Φ.length - 2, Φ.length - 1)
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ i₁) .full) i₁ (K.conjE fun Γ Φ ψ ↦
        let (b, bR) := (Φ.length - 2, Φ.length - 1)
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ i₂) .full) i₂ (K.conjE fun Γ Φ ψ ↦
          let (f, fR) := (Φ.length - 2, Φ.length - 1)
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ i₃) .full) i₃ (K.conjE fun Γ Φ ψ ↦
            let (s, sR) := (Φ.length - 2, Φ.length - 1)
            k b bR f fR s sR Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let cons : Deducer := dImpI L <| dImpI L <| dImpI L <| splits fun b bR f fR s sR ↦
      dImpE L 0 (K.byHyp bR) <| K.impE (K.byHyp fR) <| K.impE (K.byHyp sR) <| normLastK K <|
      applyThm K "eraseEntry" (fun Γ ↦ [atPos 1 Γ, atPos 0 Γ])
        [K.byHyp b, K.byHyp f, K.byHyp s] <| normLastK K <|
      linkK K "eraseEntriesMap: a construction" K.byNorm
    let d₁ ← linkK K "eraseEntriesMap: a construction" cons [list treeTy, treeTy, T.envTy]
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The erasure fixes a list of entries each fixed ({name}`eraseEntry`): its forced map is the list
({name}`eraseEntriesMap`); its head a list's, which the step's tests of a keyword's naming reject.
In the context of the list and the typing environment. -/
def eraseEntries (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("eraseEntries", fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let Γ := [list treeTy, T.envTy]
    let step ← eraseStepIdx K
    let tl := pc P "Typing.tList" [v 0]
    let a : Internal.Thm := ⟨0, Γ, [S.allL (binderEntry P (v 1)) (v 0), S.allL (flagEntry P) (v 0),
      S.allL (shapeEntry P) (v 0)], Term.eq (pc P "Datatype.eraseExpr" [tl]) tl⟩
    let byS : Deducer := fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ [.delta step]) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let split (h : ℕ) (k : ℕ → ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h (K.conjE fun Γ Φ ψ ↦
        k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    let some d := (fun Γ Φ ψ ↦ K.listCase treeTy (atPos 1 Γ) (linkK K "eraseEntries: empty" byS)
          (fun Γ Φ ψ ↦
            let (hd, rest) := (atPos (Γ.length - 2), atPos (Γ.length - 1))
            split 0 (fun b bR ↦ split 1 fun f fR ↦ split 2 fun s sR ↦
              K.cutThm "eraseEntriesMap" (fun Γ ↦ [rest Γ, atPos 0 Γ]) <|
              K.impE (K.byHyp bR) <| K.impE (K.byHyp fR) <| K.impE (K.byHyp sR) <| normLastK K <|
              fun Γ Φ ψ ↦ K.treeNode (hd Γ) (normLastK K fun Γ Φ ψ ↦
                dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
                  if bs.map Oitavem.rank == some 2 then
                    applyThm K "eraseEntry" (fun Γ ↦ [hd Γ, atPos 0 Γ])
                      [K.byHyp b, K.byHyp f, K.byHyp s] <| normLastK K <|
                    K.cutThm "eraseHead" (fun Γ ↦ [consT treeTy (hd Γ) (rest Γ)]) <| normLastK K <|
                    linkK K "eraseEntries: the list" (splitGoal K K.byNorm)
                  else linkK K s!"eraseEntries: the label {bs.map Oitavem.rank}"
                    (K.hypFalse b))
                  3 [] (v 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "eraseEntries: not proved" fun _ ↦ none
    pure (a, d))

/-- The flags of a structural recursion's clause's metadata's entries each a numeral's atom. -/
def flagHyps (P : Prog) (S : Defs) (md : Term) : List Term :=
  [S.allL (flagEntry P) (metaAt P md 1), S.allL (flagEntry P) (metaAt P md 2)]

/-- The entries of a structural recursion's clause's metadata each without a third element. -/
def shapeHyps (P : Prog) (S : Defs) (md : Term) : List Term :=
  [S.allL (shapeEntry P) (metaAt P md 1), S.allL (shapeEntry P) (metaAt P md 2)]

/-- The erasure keeps the parts of a structural recursion's clause's metadata
({name}`eraseMetaWith`). -/
def cataEraseMeta (P : Prog) (S : Defs) (T : Defs3) : Step :=
  eraseMetaWith "cataEraseMeta" "eraseEntries" binderEntry
    (fun P md ↦ flagHyps P S md ++ shapeHyps P S md) (fun h ↦ [h, h + 2, h + 4]) P S T

/-- The list value of a structural recursion's suspended results {lit}`rs` of the type
{lit}`A`. -/
def resultsVal (P : Prog) (A rs : Term) : Term := pc P "Eval.ofList" [A, rs]

/-- What a structural recursion's test depends on: the node, after the unit argument's and the
results' names in the scope and values in the environment. -/
def cataTest (P : Prog) : TestSpec where
  sv := pc P "Datatype.aO" []
  svName := nodeName P
  scope := cataNames P
  index := "aOIndex"
  atoms := [("aEqNotNumeral", pc P "Datatype.aEq" []),
    ("aLabelNotNumeral", pc P "Datatype.aLabel" []), ("aONotNumeral", pc P "Datatype.aO" [])]
  res := "cataTestRes"
  nums := "cataTestNums"
  conv := "cataTestConv"
  env := fun t e ↦ consT treeTy (v 5) (consT treeTy (v 4)
    (consT treeTy (pc P "Eval.valQuote" [t]) e))
  envCtx := [treeTy, treeTy]
  lookups := ["nthTwo3"]

/-- The program of the chain of a structural recursion's clauses: the case analysis's, the clause's
fields' typing kept folded. -/
def cataChainProg (P : Prog) : Prog :=
  { chainProg P with folded := (chainProg P).folded ++ ["Typing.cataFields"] }

/-- The chain of a structural recursion's clauses, at the walk's parts {lit}`w`: the recursion's
entries around them; the further variables the datatype's atom, the result type's form, the
default's form, the suspended results, their type and the unit value; the common type the result
type. -/
def cataChainSpec (P : Prog) (S : Defs) (T : Defs3) (w : WalkParts) : ChainSpec :=
  let Q := cataChainProg P
  let erasure (ex : ℕ → Term) (md b : Term) : Term :=
    cataClauseStep Q (ex 2) (ex 3) (cataBinds Q w md b (ex 2) (ex 3))
  { name := "cataChain"
    prog := Q
    test := cataTest Q
    extra := [treeTy, treeTy, treeTy, list treeTy, treeTy, treeTy]
    cx := fun ex inner ↦ cataScope Q (ex 0) inner
    env := fun ex t e ↦ consT treeTy (ex 6) (consT treeTy (resultsVal Q (ex 5) (ex 4))
      (consT treeTy (pc Q "Eval.valQuote" [t]) e))
    base := fun ex ↦ cataScope Q (ex 0) (nilT treeTy)
    fields := fun ex E ↦ Term.lam treeTy (Term.lam treeTy (Term.lam (exp (list treeTy) treeTy)
      (Term.lam (list treeTy) (pc Q "Typing.cataFields" [sh 4 E, sh 4 (ex 1), sh 4 (ex 0),
        v 3, v 2, v 1, v 0]))))
    bind := fun ex ↦ Term.lam treeTy (Term.lam treeTy
      (erasure (fun i ↦ sh 2 (ex i)) (v 1) (v 0)))
    erasure := erasure
    fixedVar := fixedEntry Q
    metaExtra := fun md ↦ flagHyps Q S md ++ shapeHyps Q S md
    extraHyps := fun ex ↦ [T.numsT (v 5) (v 8), T.namesT (v 9),
      lenEqT Q (call D.children [] [v 3]) (ex 4),
      relatedT Q T (v 5) (ex 1) (v 10) (ex 0) (call D.children [] [v 3]) (ex 4)]
    clauseAt := "cataClauseAt"
    fieldsNothing := "cataFieldsNothing"
    walkBinders := "cataWalkBinders"
    eraseMeta := "cataEraseMeta"
    fieldsDef := "Typing.cataFields"
    walkDefs := ["Reader.numeral"]
    cxWalk := fun ex inner ↦ consT treeTy (fieldsEntry Q)
      (consT treeTy (splitEntry Q (ex 0)) (cataScope Q (ex 0) inner))
    walkExtra := fun ex ↦ [ex 1, ex 0, ex 2, ex 3]
    testExtra := fun ex ↦ [resultsVal Q (ex 5) (ex 4), ex 6]
    clause := "cataClause"
    clauseArgs := fun ex ↦ [ex 1, ex 0, ex 2, ex 3]
    clauseFlags := flagHyps Q S
    preHyps := [0, 1]
    clauseAlls := fun ex ↦ [ex 4, ex 5, ex 6]
    midHyps := [2, 3]
    svExcluded := "nodeExcluded"
    scopeNames := [(unitName Q, ((cataExcluded Q).find? (·.1 == unitName Q)).elim "" (·.2)),
      (resultsName Q, "resultsExcluded")] }

/-- A step of the specification {name}`cataChainSpec`, at the walk's parts. -/
def withWalkParts (name : String) (P : Prog) (S : Defs) (T : Defs3)
    (f : ChainSpec → Step) : Step :=
  (name, fun ix E ↦ do
    let w ← cataWalkParts ⟨cataVarProg P, S, E, ix, []⟩ T
    (f (cataChainSpec P S T w)).2 ix E)

/-- The development of the chain of a structural recursion's clauses. -/
def cataChainDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [eraseEntry P S T, eraseEntriesMap P S T, eraseEntries P S T, cataEraseMeta P S T,
    notNumeral P S "aONotNumeral" (pc P "Datatype.aO" []),
    indexLemma P S "aOIndex" [list treeTy] (nodeName P) (cataNames P (v 0)),
    testResAt (cataTest P) P S T, testNumsAt (cataTest P) P S T, testConvAt (cataTest P) P S,
    withWalkParts "cataClauseAt" P S T fun c ↦ clauseAtWith c S T,
    withWalkParts "cataChain" P S T fun c ↦ chainWith c S T]

/-- The soundness at the chain of a structural recursion's clauses, after its clauses'. -/
def cataChainCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := caseNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (caseDev P S T).map (·.1) ++ (clausesDev P S T).map (·.1) ++
    (caseSoundDev P S T).map (·.1) ++ (cataDev P S T).map (·.1) ++
    (cataClausesDev P S T).map (·.1)) "datatype-cata-chain" (cataChainDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
