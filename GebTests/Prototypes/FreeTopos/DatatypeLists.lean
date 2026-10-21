/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeAssembly
public meta import GebTests.Prototypes.FreeTopos.DatatypeAssembly -- shake: keep
public import GebTests.Prototypes.FreeTopos.DatatypeData
public import GebTests.Prototypes.FreeTopos.DatatypeFolds
public meta import GebTests.Prototypes.FreeTopos.DatatypeData -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at every list

The soundness of the datatype language's stage-1 compiler
({lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`) at every list, from that at its elements. A
list headed by a keyword whose forms the developments before prove sound
({lit}`keywordCases`) is sound ({lit}`kwList`): its further elements split until they are as
many as the forms take, any other number refuted by the typing, each element's expansion decided
present first; for more elements than the form takes, the inequalities of a length with the
numerals four and five ({lit}`neqMore`). The lists headed by the keywords of the kernel's
constants are sound by
{name}`GebTests.Prototypes.FreeTopos.Datatypes.constSrc`. Every list is sound ({lit}`listCase`),
given that at its elements and at the lists headed by the keywords later developments prove sound
({lit}`laterKeywords`): the empty list refuted; an atom's name decided against each keyword's,
a list headed by an atom no keyword names sound by
{name}`GebTests.Prototypes.FreeTopos.Datatypes.appAtom`; a list headed by a list by
{name}`GebTests.Prototypes.FreeTopos.Datatypes.appList`; and a head of any other label, whose
expansion is the leaf 0, by the soundness of applications.

## Main definitions

* {lit}`kwList`, {lit}`listCase` — the soundness at a list headed by a keyword, and at every list.
* {lit}`listsCertificates` — the development, stored as the certificate {lit}`datatype-lists`.

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

/-- The keywords whose forms the developments before prove sound, each with its number of
elements and its soundness's name. -/
def keywordCases : List (String × ℕ × String) :=
  [("Reader.kwLet", 4, "letCase"), ("Reader.kwQuote", 1, "quoteCase"),
    ("Reader.kwNil", 1, "nilCase"), ("Reader.kwIf", 3, "ifCase"),
    ("Reader.kwCons", 2, "consCase"), ("Reader.kwFst", 1, "fstCase"),
    ("Reader.kwSnd", 1, "sndCase"), ("Reader.kwPair", 2, "pairCase"),
    ("Reader.kwLam", 2, "lamCase"), ("Typing.kwRep", 1, "repCase")]

/-- The inequalities of a bitstring's successors with the numerals four and five
({name}`GebTests.Prototypes.FreeTopos.Normalization.eqnLemmas`), which the arities of the forms of
four further elements compare a list's length with: by case analysis of the innermost bitstring,
with the inequalities before. -/
def neqMore (P : Prog) : List Step :=
  let rs := foldedRules P
  let sc (t : Term) : Term := call D.succ [] [t]
  let neq (n : ℕ) : Internal.Thm :=
    nfThm P rs [bitsTy] (call D.eqB [] [n.rec (sc (v 0)) fun _ t ↦ sc t, numeral n]) bnilT
  let byBit (n : ℕ) (a : Internal.Thm) (ix : String → ℕ) (E : Array Internal.Entry) :
      Option Internal.Deriv :=
    let rules := (List.range n).map (fun k ↦ Internal.NormRule.thm (ix s!"neq{k}") []) ++
      rebRules ix ++ foldedRules P
    let p : Internal.Prover := fun Γ Φ t u ↦ byMode .full P.G E 0 rules Γ Φ t u
    byListSplit P.G 0 0 p (bySplit2 3 4 1 p p) a.ctx [] (TranslationProofs.sides a).1
      (TranslationProofs.sides a).2
  [4, 5].map fun n ↦ step s!"neq{n}" (neq n) (byBit n (neq n))

/-- The soundness at a list headed by the keyword {lit}`kw` ({name}`kwListThm`), the soundness at
its forms of {lit}`n` further elements {lit}`thm`: the further elements split by cases until there
are {lit}`n`, the soundness at that form, its elements' soundness the hypothesis split; any other
number refuted, the statement's hypotheses introduced, by the tests of the list's expansion, its
typing and its test of source forms decided ({name}`splitSolve`). -/
def kwList (P : Prog) (S : Defs) (T : Defs3) (kw : String) (n : ℕ) (thm : String) : Step :=
  (kwListName kw, fun ix E ↦ do
    let K := appKit P S ix E
    let a := kwListThm P S T kw
    let last : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    -- a number of elements refuted: the statement's hypotheses introduced, each element's
    -- expansion decided present, the first first, else the list's absent; all present, the
    -- list's typing absent, else the tests of the expansion, the typing and the source form
    -- decided
    let refute (msg : String) (ps : List ℕ) : Deducer :=
      refuteForm P S T K s!"{kwListName kw}: {msg}" ps
        (["neq4", "neq5"].map fun nm ↦ Internal.NormRule.thm (ix nm) [])
    -- the hypothesis, the soundness at every element, split into the elements' soundness
    let splitAll : Deducer → Deducer := fun k Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 ((List.range n).foldr
        (fun _ k Γ Φ ψ ↦ (K.conjE k Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ) k) Γ Φ ψ
    -- the soundness at the form of the elements of the positions ps
    let form (ps : List ℕ) : Deducer := splitAll fun Γ Φ ψ ↦ do
      let some (Internal.Entry.language b) := K.E[K.ix thm]? | none
      let σ := ps.map fun p ↦ atPos p Γ
      let prems ← b.hyps.mapM fun h ↦ anyHyp Γ Φ (Internal.instTerm [] σ h)
      dCut (Internal.instTerm [] σ b.concl) (nd (.apply (K.ix thm) [] σ) prems) last Γ Φ ψ
    -- the remaining elements, at the position tl, split; the positions of those split before
    let some d := (List.range (n + 1)).foldr (fun i (rec : ℕ → List ℕ → Deducer) tl ps ↦
          fun Γ Φ ψ ↦ K.listCase treeTy (atPos tl Γ)
            (if i = n then form ps else refute s!"{i} elements" ps)
            (fun Γ' Φ' ψ' ↦ if i = n then refute "more elements" ((Γ'.length - 2) :: ps) Γ' Φ' ψ'
              else rec (Γ'.length - 1) ((Γ'.length - 2) :: ps) Γ' Φ' ψ') Γ Φ ψ)
        (fun _ _ ↦ fun _ _ _ ↦ none) 0 [] a.ctx a.hyps a.concl
      | dbgTrace s!"{kwListName kw}: not proved" fun _ ↦ none
    pure (a, d))

/-- The keywords whose forms later developments prove sound, which the soundness at lists takes
as hypotheses. -/
def laterKeywords : List String :=
  ["Typing.kwDatum", "Typing.kwDecode", "Datatype.kwCase", "Datatype.kwCata"]

/-- The soundness at every list headed by the keyword {lit}`kw`, given that at its further
elements. -/
def headedφ (P : Prog) (S : Defs) (T : Defs3) (kw : String) : Term :=
  Internal.Logic.all P.o (list treeTy) (Term.lam (list treeTy) (Internal.Logic.imp P.o
    (S.allL (Term.lam treeTy (datatypeφ P S T)) (v 0))
    (Internal.instTerm [] [listOf (kwAtom P kw) (v 0)] (datatypeφ P S T))))

/-- The soundness at a list, in the context of its elements, given that at each element and that
at every list headed by a keyword of {name}`laterKeywords`. -/
def listCaseThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  ⟨0, [list treeTy],
    S.allL (Term.lam treeTy (datatypeφ P S T)) (v 0) :: laterKeywords.map (headedφ P S T),
    Internal.instTerm [] [nodeT (Term.pair (numeral 2) (v 0))] (datatypeφ P S T)⟩

/-- The soundness at a list ({name}`listCaseThm`): the list empty, refuted by its typing; else its
head decided: an atom named by a keyword of {name}`laterKeywords`, the hypothesis, or by any other
keyword, the soundness at the lists that keyword heads ({name}`kwList`, {name}`constSrc`); an atom
named by none, {name}`appAtom`; a list, {name}`appList`; a node of any other label, whose expansion
is the leaf 0, which has no type, the soundness of applications at source forms at it, its own
soundness refuted. -/
def listCase (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("listCase", fun ix E ↦ do
    let K := appKit P S ix E
    let L := K.L
    let a := listCaseThm P S T
    let childrenT ← primT Kernel.Prim.children
    let unfold := ((List.range nFolds).map T.argIdx ++
      ["Typing.synList", "Reader.resolveList"].map P.idx).map Internal.NormRule.delta
    let last : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    -- the instance of a theorem with hypotheses, each proved by its deducer, cut in
    let W₀cut (name : String) (σ : List Tree → List Term) (prems : List Deducer) (k : Deducer) :
        Deducer := fun Γ Φ ψ ↦ do
      let some (Internal.Entry.language b) := K.E[K.ix name]? | none
      let ds ← (b.hyps.zip prems).mapM fun (h, d) ↦ d Γ Φ (Internal.instTerm [] (σ Γ) h)
      dCut (Internal.instTerm [] (σ Γ) b.concl) (nd (.apply (K.ix name) [] (σ Γ)) ds) k Γ Φ ψ
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    -- a list refuted: the statement's hypotheses introduced, the tests of its expansion, its
    -- typing and its test of source forms decided until one of them is false
    let refuteAt (msg : String) : Deducer := refuteStatement P S T K s!"listCase: {msg}"
    -- the hypothesis of index h, the soundness at every element of a list split into its
    -- elements, each element's soundness after the hypotheses
    let splitAll (h n : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h ((List.range n).foldr
        (fun _ k Γ Φ ψ ↦ (K.conjE k Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ) k) Γ Φ ψ
    -- a list headed by a tree of a label neither an atom's nor a list's, whose expansion is the
    -- leaf 0: the statement's quantifiers and hypotheses introduced, the application's soundness
    -- at source forms (appSrc) at the head, the head's soundness by refutation, as the leaf 0 has
    -- no type, and no keyword naming the head or its expansion by normalization and case
    -- analyses
    let other (rs hd : List Tree → Term) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let W₀ := kwKit P S T ix E Γ₀.length (List.replicate Φ₀.length true)
      let W := { W₀ with K := K }
      let app : Deducer :=
        W₀cut "appSrc" (fun Γ ↦ [rs Γ, hd Γ])
          [refuteAt "the head's soundness at another label", anyHyp] fun Γ Φ ψ ↦
          dAllE L K.G K.E (Φ.length - 1) (W.qv 1 Γ) (((List.range (nQ - 1)).foldr
            (fun j k ↦ K.allEΓ (W.qv (j + 2)) k) <|
            (List.range W.nH).foldr (fun i k ↦ K.impE (K.byHyp (W.hyp i)) k) <|
            (List.range (srcFree P T).length).foldr (fun j k ↦
              K.impE (linkK K s!"listCase: keyword {j} at another label"
                (dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold) .full)
                  (splitSolve K (fun Φ ↦ K.rules Φ ++ unfold) (fun _ ↦ []) 12 [] .head))) k) <|
            last)) Γ Φ ψ
      ((List.range nQ).foldr (fun _ k ↦ dAllI L k) ((List.range W.nH).foldr (fun _ k ↦ dImpI L k)
        app)) Γ₀ Φ₀ ψ₀
    -- the list's elements, its head and its rest, its head's label and elements, by position
    let cons : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
      let (hPos, tPos) := (Γ₁.length - 2, Γ₁.length - 1)
      -- the head's and the rest's soundness, after the hypotheses
      splitAll 0 1 (fun Γ Φ ψ ↦
      K.treeNode (atPos hPos Γ₁) (fun Γ₂ Φ₂ ψ₂ ↦
        let (lPos, hcsPos) := (Γ₂.length - 2, Γ₂.length - 1)
        let hcs (Γ : List Tree) : Term := atPos hcsPos Γ
        let rs (Γ : List Tree) : Term := atPos tPos Γ
        let X := ((evalRw K.G K.E (K.rules Φ₂) .full Γ₂ Φ₂ (call D.lab [] [atPos hPos Γ₂])).map
          Prod.fst).getD (atPos lPos Γ₂)
        -- an atom: its name decided against each keyword's
        let atomCase : Deducer :=
          let name (Γ : List Tree) : Term := nameOfChars P (hcs Γ)
          headKeywords.foldr (fun kw k ↦
            decideBits K (fun Γ ↦ call D.equal [] [name Γ, pc P kw []]) k
              (linkK K s!"listCase: the keyword {kw}" <|
              K.cutThm "equalSound" (fun Γ ↦ [name Γ]) <| K.allEΓ (fun _ ↦ pc P kw []) <|
              K.impE (K.solve 3) fun Γ Φ ψ ↦
              K.image (Φ.length - 1) (fun t ↦ apps childrenT [t]) (fun Γ Φ ψ ↦
                match laterKeywords.idxOf? kw with
                | some j =>
                  dAllE L K.G K.E (1 + j) (rs Γ) (K.impE anyHyp last) Γ Φ ψ
                | none =>
                  W₀cut (kwListName kw) (fun Γ ↦ [rs Γ]) [anyHyp] last Γ Φ ψ) Γ Φ ψ))
            (linkK K "listCase: an atom" <|
              W₀cut "appAtom" (fun Γ ↦ [rs Γ, hcs Γ])
                ([anyHyp, anyHyp] ++ headKeywords.map fun _ ↦ K.solve 3) last)
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          match bs.map Oitavem.rank with
          | some 1 => K.norm atomCase
          | some 2 => linkK K "listCase: a list" <|
              W₀cut "appList" (fun Γ ↦ [rs Γ, hcs Γ]) [anyHyp, anyHyp] last
          | _ => linkK K "listCase: a head of another label" (other rs (atPos hPos)))
            2 [] X Γ₂ Φ₂ ψ₂) Γ Φ ψ) Γ₁ Φ₁ ψ₁
    let some d := K.listCase treeTy (v 0) (refuteAt "the empty list") cons a.ctx a.hyps
        a.concl
      | dbgTrace "listCase: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness at every list: the inequalities of lengths with the numerals
four and five, the soundness at the lists headed by each keyword of {name}`keywordCases`, and at
every list. -/
def listsDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  neqMore P ++ keywordCases.map (fun (kw, n, thm) ↦ kwList P S T kw n thm) ++ [listCase P S T]

/-- The development of the soundness at every list ({name}`listsDev3`), after the base's, the
atom's, the list's, the stage functions' at applications, the applications', the list
expansion's, the soundness at applications', the abstractions' over one binder and over lists of
binders, the representations', and the kernel's constants', stored as the certificate
{lit}`datatype-lists`. -/
def listsCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (stagesDev3 P S T).map (·.1) ++ (applyDev3 P S T).map (·.1) ++
    (expansionDev3 P S T).map (·.1) ++ (assemblyDev3 P S T).map (·.1) ++
    (appDev3 P S T).map (·.1) ++ (lamDev3 P S T).map (·.1) ++ (dataDev3 P S T).map (·.1) ++
    (foldsDev3 P S T).map (·.1))
    "datatype-lists"
    (listsDev3 P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
