/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeAssembly
public meta import GebTests.Prototypes.FreeTopos.DatatypeAssembly -- shake: keep
public import GebTests.Prototypes.FreeTopos.DatatypeLam
public meta import GebTests.Prototypes.FreeTopos.DatatypeLam -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at the representations of members

The soundness of the datatype language's stage-1 compiler
({lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`) at the representation of a datatype's member as
a tree. The erasure writes the representation of a term as the list of the term alone, which the
stages after it read as the term's application to no arguments; the representation's erasure is
that of the list of the term's expansion alone, so that the soundness there follows from that at
applications at expanded forms ({name}`GebTests.Prototypes.FreeTopos.Datatypes.appCore`), the
term's expansion named by no keyword as each stage reads it; and a value related at a datatype, a
member's quotation, is related at the tree type ({lit}`relTDataTree`).

## Main definitions

* {lit}`relTDataTree` — a value related at a datatype is related at the tree type.
* {lit}`repCase` — the soundness at a representation.
* {lit}`dataCertificates` — the development, stored as the certificate {lit}`datatype-data`.

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

/-- A value related at a datatype, a type the typing's test of datatypes accepts, is related at the
tree type: the type a node, its label decided by the test; at the label of datatypes the relation
unfolded, a member's quotation, a tree's quotation by {name}`relTTree`. In the context of the
value, the type and the relation's context. -/
def relTDataTree (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relTDataTree", fun ix E ↦ do
    let o := P.o
    let K : Kit := ⟨P, S, E, ix, (vocab3 ++ ["relTTree"]).filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size⟩
    let L := K.L
    let Γ := [treeTy, treeTy, Defs3.ctxTy]
    let a : Internal.Thm := ⟨0, Γ, [],
      Internal.Logic.imp o (truth o (pc P "Typing.isData" [v 1])) <|
      Internal.Logic.imp o (Term.app (T.relT (v 2) (v 1)) (v 0)) <|
      Term.app (T.relT (v 2) (leafT bnilT)) (v 0)⟩
    -- the relation unfolded at the datatype: a member's quotation, a tree's
    let data : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 1 ++ [.delta T.q]) .full) 1 (K.exE <| K.conjE <|
        fun Γ Φ ψ ↦ K.norm (dExI L K.G K.E (atPos (Γ.length - 1) Γ) (K.solve 3)) Γ Φ ψ) Γ Φ ψ
    let some d := verifyK K "relTDataTree" (linkK K "relTDataTree" (dImpI L (dImpI L
        (linkK K "relTDataTree: node" (K.treeNode (v 1) (K.splitHyp 0
          (linkK K "relTDataTree: data" data) 8)))))) a.ctx a.hyps a.concl
      | dbgTrace "relTDataTree: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at a representation, at source forms, given that at its term: the test of the
keyword's characters, fixed by the expansion of numeral abbreviations, computed; the term's label
decided. An atom is its own expansion: its name decided against each keyword the typing reads, a
keyword's refuting the typing; its characters fixed, else the test of source forms is refuted;
an abbreviation's numeral named by no reader's keyword ({name}`numeralUnnamed`). A list's
expansion, present, generalized, is a list ({name}`expList`), and so are its erasure
({name}`eraseList`) and that erasure with the numeral abbreviations expanded
({name}`numsListThm`); the test of source forms of the list of the expansion alone, the typing's
form of the expansion a list, each cut in while the expansion is a variable, the keywords' tests
with the expansion a node in their own proofs, as at the head of an application of a list
({name}`appList`). A tree of any other label refutes the typing. Then the expansion's type
present, generalized, a datatype's; the soundness at the list of the expansion alone at expanded
forms ({name}`appCore`), whose erasure is the representation's, its antecedents the statement's
with the stage functions' steps unfolded, its value related at the tree type by
{lit}`relTDataTree`. The keyword's being a numeral abbreviation is immaterial, the erasure dropping
it before the abbreviations are expanded. -/
def repCase (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("repCase", fun ix E ↦ do
    let kw := "Typing.kwRep"
    let W₀ := kwKit P S T ix E 1 [true] kw
    let K := { W₀.K with more := W₀.K.more ++ ["applyTyCons", "appsCons"] }
    let W := { W₀ with K := K }
    let L := K.L
    let a := kwThm P S T kw 1
    let childrenT ← primT Kernel.Prim.children
    let nK := (headFree P T).length
    let unfold := ((List.range nFolds).map T.argIdx ++
      [P.idx "Typing.synList", P.idx "Reader.resolveList"]).map Internal.NormRule.delta
    let refute (msg : String) : Deducer := linkK K s!"rep: {msg}" fun Γ Φ ψ ↦
      (anyFalse K Γ Φ ψ).orElse fun _ ↦ (W.hypFalseU (W.hyp 6) Γ Φ ψ).orElse fun _ ↦
        W.hypFalseU (W.hyp 4) Γ Φ ψ
    let nums (Γ : List Tree) : Term := W.qv 7 Γ
    let fnOf (Γ : List Tree) : Term :=
      Term.lam treeTy (pc P "Reader.expandNums" [Term.rename (nums Γ) (· + 1), v 0])
    -- a hypothesis and the goal normalized with the steps unfolded
    let byHypWith (h : ℕ) (unfold : List Internal.NormRule) : Deducer := fun Γ Φ ψ ↦
      (K.byHyp h Γ Φ ψ).orElse fun _ ↦
      let rs := (K.rulesEx Φ h ++ unfold)
      (dRwHyp (evalRw K.G K.E rs .full) h
        (dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold) .full) dHyp) Γ Φ ψ).orElse fun _ ↦
      let nf (rs : List Internal.NormRule) (t : Term) : Option Term :=
        (evalRw K.G K.E rs .full Γ Φ t).map Prod.fst
      let d := ((Φ[h]?).bind (nf rs)).bind fun a ↦ (nf (K.rules Φ ++ unfold) ψ).bind fun b ↦
        firstDiff a b
      dbgTrace s!"rep: hypothesis {h}: {d.map fun (a, b) ↦ s!"{showT a}\n  vs {showT b}"}"
        fun _ ↦ none
    let byHypU (h : ℕ) : Deducer := byHypWith h unfold
    let renormLast (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1)) .full) (Φ.length - 1) k Γ Φ ψ
    -- the soundness at the list of the expansion X alone, its antecedents the statement's, the
    -- source forms' test by src, its keyword tests by kws, its conclusion's value, of the type
    -- of position yPos, related at the tree type
    let use (X : List Tree → Term) (src : Deducer) (kws : ℕ → Deducer) (yPos : ℕ) : Deducer :=
      fun Γ Φ ψ ↦
      let solveU : Deducer := fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦
        ([unfold, [.delta (T.argIdx 1), .delta (P.idx "Typing.synList")]].findSome? fun u ↦
          dRwBy (evalRw K.G K.E (K.rules Φ ++ u) .full) (K.solve 3) Γ Φ ψ)
      let ante (i : ℕ) : Deducer :=
        if i = 5 ∨ i = 6 then solveU else if i = 4 then src
        else if i = 7 ∨ i = 8 then fun Γ Φ ψ ↦
          (byHypWith (W.hyp i) [.delta (T.argIdx 2), .delta (T.argIdx 3)] Γ Φ ψ).orElse fun _ ↦
            byHypU (W.hyp i) Γ Φ ψ
        else W.byStmt i
      let concl : Deducer := K.unfoldConv <| K.exE <| K.exE <| K.conjE fun Γ Φ ψ ↦
        let (nPos, wPos) := (Γ.length - 2, Γ.length - 1)
        let (iS, iR) := (Φ.length - 2, Φ.length - 1)
        K.norm (dConv L K.G K.E S (atPos nPos Γ) (atPos wPos Γ)
          (linkK K "rep: stable" fun Γ Φ ψ ↦
            dAllE L K.G K.E iS (v 0) (fun Γ Φ ψ ↦ byHypU (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
          (linkK K "rep: related" <|
            K.cutThm "relTDataTree" (fun Γ ↦ [atPos wPos Γ, atPos yPos Γ, W.qv 10 Γ]) <|
            K.impE (linkK K "rep: a datatype" (K.solve 3)) <|
            K.impE (linkK K "rep: the relation" (byHypU iR)) <|
            linkK K "rep: at the tree type" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ
      (W.cutApply "expSound" (fun Γ ↦ [atPos 0 Γ]) [K.byHyp 0] <|
        K.allEΓ (W.qv 3) <| K.impE (K.solve 3) fun Γ Φ ψ ↦
        W.cutApply "appCore" (fun Γ ↦ [nilT treeTy, X Γ])
          [K.byHyp (Φ.length - 1), K.solve 3] (fun Γ Φ ψ ↦
          dAllE L K.G K.E (Φ.length - 1) (W.qv 1 Γ) (((List.range (nQ - 1)).foldr
            (fun j k ↦ K.allEΓ (W.qv (j + 2)) k) <|
            (List.range W.nH).foldr (fun i k ↦
              K.impE (linkK K s!"rep: antecedent {i}" (ante i)) k) <|
            (List.range nK).foldr (fun j k ↦ K.impE (linkK K s!"rep: keyword {j}" (kws j)) k) <|
            linkK K "rep: the conclusion" concl)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    -- the expansion's type present, generalized, a datatype's
    let typed (X : List Tree → Term) (src : Deducer) (kws : ℕ → Deducer) : Deducer :=
      fun Γ Φ ψ ↦
      (W.presentAt "the term's type" (fun Γ ↦ pc P "Typing.synIn" [W.qv 4 Γ, W.qv 5 Γ, X Γ])
        (W.hyp 6) (W.hyp 6) (fun Γ Φ ψ ↦
        let yPos := Γ.length - 1
        decideIn K (fun Γ ↦ pc P "Typing.isData" [atPos yPos Γ]) (refute "not a datatype")
          (use X src kws yPos) Γ Φ ψ)) Γ Φ ψ
    -- the term an atom, of the characters of position csPos, its own expansion: its name
    -- against each keyword's, the abbreviations decided
    let atom (csPos : ℕ) : Deducer :=
      let cs (Γ : List Tree) : Term := atPos csPos Γ
      let X (Γ : List Tree) : Term := atomOf (cs Γ)
      let nm (Γ : List Tree) : Term := nameOfChars P (cs Γ)
      let kws (_ : ℕ) : Deducer := fun Γ Φ ψ ↦
        dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold) .full) (K.solve 3) Γ Φ ψ
      let typedA := typed X (kws 0) kws
      let abbreviated : Deducer :=
        linkK K "rep: the abbreviation" <|
        dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) (W.hyp 2) fun Γ Φ ψ ↦
        dAllE L K.G K.E (Φ.length - 1) (nm Γ) (K.conjE fun Γ Φ ψ ↦
          let (n₁, n₂) := (Φ.length - 2, Φ.length - 1)
          dImpE L n₂ (K.solve 3) (fun Γ Φ ψ ↦
            dImpE L n₁ (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) (K.exE <| K.conjE fun Γ Φ ψ ↦
              let iNum := Φ.length - 1
              let dsPos := Γ.length - 1
              (readerKeywords.foldr (fun kw k ↦ W.cutApply s!"numeralUnnamed/{kw}"
                  (fun Γ ↦ [atPos dsPos Γ]) [K.byHyp iNum] k) typedA) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
          Γ Φ ψ
      typingKeywords.foldr (fun kw k ↦
        decideBits K (fun Γ ↦ call D.equal [] [nm Γ, pc P kw []]) k
          (linkK K s!"rep: the keyword {kw}" <|
          K.cutThm "equalSound" (fun Γ ↦ [nm Γ]) <| K.allEΓ (fun _ ↦ pc P kw []) <|
          K.impE (K.solve 3) fun Γ Φ ψ ↦
          K.image (Φ.length - 1) (fun t ↦ apps childrenT [t])
            (refute s!"the keyword {kw}") Γ Φ ψ))
        (decideIn K (fun Γ ↦ pc P "charsFixed" [fnOf Γ, cs Γ]) (refute "characters not fixed") <|
          K.cutThm "charsFixedEq" (fun Γ ↦ [cs Γ, nums Γ]) <| K.impE (K.solve 3) <|
          decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [nm Γ, nums Γ]])
            typedA abbreviated)
    -- the term a list, of the elements of position hcsPos: its expansion present, generalized,
    -- a list (expList); the source forms' test of the list of the expansion alone cut in while
    -- the expansion is a variable; the expansion a node of that label; no keyword naming it as
    -- each stage reads it, as at the head of an application of a list (appList)
    let listT (hcsPos : ℕ) : Deducer :=
      let hcs (Γ : List Tree) : Term := atPos hcsPos Γ
      let expH (Γ : List Tree) : Term :=
        pc P "Datatype.expandExpr" [W.qv 3 Γ, nodeT (Term.pair (numeral 2) (hcs Γ))]
      let unfoldJ (j : ℕ) := ((List.range nFolds).filter (j < 4 ∨ 0 < ·)).map fun k ↦
        Internal.NormRule.delta (T.argIdx k)
      -- the keyword test of index j, as appList proves those after the first five of srcFree
      let fact (X : List Tree → Term) (j : ℕ) : Deducer := fun Γ Φ ψ ↦
        let nT := typingKeywords.length
        if j < nT then
          dRwBy (evalRw K.G K.E (K.rules Φ ++ unfoldJ (j + 5)) .full)
            (splitSolve K (fun Φ ↦ K.rules Φ ++ unfoldJ (j + 5)) (fun _ ↦ []) 12 [] .head) Γ Φ ψ
        else do
          let eras := j < nT + erasureKeywords.length
          let kw := if eras then erasureKeywords.getD (j - nT) ""
            else readerKeywords.getD (j - nT - erasureKeywords.length) ""
          let g := pc P "Datatype.eraseExpr" [pc P "Prelude.get" [expH Γ]]
          let nf (t : Term) : Option Term := (evalRw K.G K.E (K.rules Φ) .full Γ Φ t).map Prod.fst
          let some (view, nmsV) := (if eras then [(g, g)] else
              (List.range Γ.length).map fun i ↦ (pc P "Reader.expandNums" [v i, g], v i)).find?
                fun (y, _) ↦ nf (unnamed P y kw) == nf ψ
            | dbgTrace s!"rep: fact {j} not a view's" fun _ ↦ none
          let numsSteps : Deducer → Deducer := if eras then id else
            W.cutApply "numsList" (fun _ ↦ [g, nmsV]) [dHyp]
          let _ := X
          W.cutApply "eraseList" (fun Γ ↦ [hcs Γ, W.qv 3 Γ]) [K.solve 3]
            (numsSteps (W.cutApply (namedListName kw) (fun _ ↦ [view]) [dHyp]
              (renormLast (K.solve 3)))) Γ Φ ψ
      W.present "the term's expansion" (fun Γ ↦ expH Γ) 5 fun Γ₀ Φ₀ ψ₀ ↦
        let X (Γ : List Tree) : Term := atPos (Γ₀.length - 1) Γ
        let srcT (Γ : List Tree) : Term := truth P.o (pc P "srcForm"
          [fnOf Γ, nodeT (Term.pair (numeral 2) (consT treeTy (X Γ) (nilT treeTy)))])
        (W.cutApply "expList" (fun Γ ↦ [hcs Γ, W.qv 3 Γ]) [K.solve 3] <| renormLast <|
          fun Γ Φ ψ ↦ do
          let d ← linkK K "rep: the list's source form"
            (byHypWith (W.hyp 4) [.delta (T.argIdx 5)]) Γ Φ (srcT Γ)
          dCut (srcT Γ) d (fun Γ Φ ψ ↦ do
            let (iLab, iSrc) := (Φ.length - 2, Φ.length - 1)
            -- each keyword test with the expansion a node of its label, within its own proof
            let factN (j : ℕ) : Deducer := fun Γ Φ ψ ↦ K.treeNode (X Γ) (fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ iLab) .full) iLab (fact X j) Γ Φ ψ) Γ Φ ψ
            -- the typing's form of the expansion a list, cut in first, which the typing of the
            -- list of the expansion alone reads
            let tForm (Γ : List Tree) : Term :=
              Term.fst (Term.app (Term.snd (T.foldAt 1 [W.qv 4 Γ] (X Γ))) Term.star)
            let φ := Term.eq (call D.lab [] [tForm Γ]) (numeral 2)
            let dT ← linkK K "rep: the typing's form a list" (fun Γ Φ ψ ↦
                K.treeNode (X Γ) (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ iLab) .full)
                  iLab (K.solve 3) Γ Φ ψ) Γ Φ ψ) Γ Φ φ
            -- the erasure of the expansion a list, and so with the numeral abbreviations expanded
            let g (Γ : List Tree) : Term := pc P "Datatype.eraseExpr" [X Γ]
            dCut φ dT (W.cutApply "eraseList" (fun Γ ↦ [hcs Γ, W.qv 3 Γ]) [K.solve 3] <|
              renormLast <| fun Γ Φ ψ ↦
              W.cutApply "numsList" (fun Γ ↦ [g Γ, nums Γ]) [K.solve 3]
                (renormLast (typed X (K.byHyp iSrc) fun j Γ Φ ψ ↦
                  (K.solve 3 Γ Φ ψ).orElse fun _ ↦ factN j Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ₀ Φ₀ ψ₀
    -- the keyword's characters fixed by the expansion of numeral abbreviations: the test's
    -- equation with its value, computed with the steps unfolded; then the term's label decided
    let decisions : Deducer := fun Γ Φ ψ ↦ do
      let t := pc P "charsFixed" [fnOf Γ, call D.children [] [pc P kw []]]
      let (l, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ t
      let rs := K.rules Φ ++ (W.ks ++ [P.idx "charsFixed"]).map Internal.NormRule.delta
      let (r, d, _) ← Internal.eval K.G K.E 0 rs 4096 .full Γ Φ l
      dCut (Term.eq l r) (nd .join [d, nd .refl]) (K.treeNode (atPos 0 Γ) fun Γ Φ ψ ↦
        let (lPos, csPos) := (Γ.length - 2, Γ.length - 1)
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          match bs.map Oitavem.rank with
          | some 1 => K.norm (atom csPos)
          | some 2 => K.norm (listT csPos)
          | _ => linkK K "rep: another label"
              (splitHead K (W.hyp 6) (fun _ _ _ ↦ none) 8 W.ks)) 2 [] (atPos lPos Γ) Γ Φ ψ)
        Γ Φ ψ
    -- the statement's hypotheses introduced; the keyword's being a numeral abbreviation is
    -- immaterial, the erasure dropping it before the abbreviations are expanded
    let some d := (List.range nQ).foldr (fun _ k ↦ dAllI L k)
        ((List.range W.nH).foldr (fun _ k ↦ dImpI L k) decisions) a.ctx a.hyps a.concl
      | dbgTrace "repCase: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness at representations: the stage functions' equations at a
representation, the relation at a datatype at the tree type, and the soundness. -/
def dataDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  kwEqs P T "Typing.kwRep" 1 ++ [relTDataTree P S T, repCase P S T]

/-- The development of the soundness at representations ({name}`dataDev3`), after the base's, the
atom's, the list's, the stage functions' at applications, the applications', the list expansion's
and the soundness at applications', stored as the certificate {lit}`datatype-data`. -/
def dataCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (stagesDev3 P S T).map (·.1) ++ (applyDev3 P S T).map (·.1) ++
    (expansionDev3 P S T).map (·.1) ++ (assemblyDev3 P S T).map (·.1)) "datatype-data"
    (dataDev3 P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
