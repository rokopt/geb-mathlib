/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeApply
public meta import GebTests.Prototypes.FreeTopos.DatatypeApply -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at applications at lists

The soundness of the datatype language's stage-1 compiler
({lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`) at the lists whose head no keyword names, from
that at their elements, in two developments.

The expansion of a list. Where it is present it is a list ({lit}`expList`): the expansion's fold
taken one step at the list, the results at the elements abstracted to a variable
({lit}`abstractUnder`), and the tests of that body and the optional values its cases are blocked
on decided ({lit}`expBody`); and where the expansion of a list headed by a list is present, so is
its head's ({lit}`expHead`).

The applications. A list headed by an atom no keyword names ({lit}`appAtom`), or by a list
({lit}`appList`), is sound by the soundness of applications at source forms
({name}`GebTests.Prototypes.FreeTopos.Datatypes.appSrc`), given that no keyword names the head as
the stages read it: as the typing reads it, by normalization and case analyses; as the erasure and
the reader read the expansion of a list, by its being a list ({lit}`eraseList`, {lit}`numsList`)
and no keyword's naming a list ({lit}`namedListThm`).

The case analyses are those of {lit}`splitSolve`: the data the normal forms of the goal and of
some hypotheses are blocked on decided, a test as a whole, an optional value as a node of a new
label and children, a list by its cases.

## Main definitions

* {lit}`splitSolve`, {lit}`refuteStatement`, {lit}`refuteForm` — a goal by normalization after
  case analyses, and the soundness at a form refuted so, or by its typing.
* {lit}`kwListThm` — the soundness at a list headed by a keyword.
* {lit}`expList`, {lit}`expHead` — the expansion of a list a list, and its head's present.
* {lit}`appAtom`, {lit}`appList` — the soundness at a list headed by an atom no keyword names, and
  by a list.
* {lit}`expansionCertificates`, {lit}`assemblyCertificates` — the developments, stored as the
  certificates {lit}`datatype-expansion` and {lit}`datatype-assembly`.

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

/-- The keywords that head a list's forms: those whose forms the typing reads, and those of case
analyses and of structural recursion, which the expansion reads. -/
def headKeywords : List String := typingKeywords ++ ["Datatype.kwCase", "Datatype.kwCata"]

/-- The atom of characters. -/
def atomOf (cs : Term) : Term := nodeT (Term.pair (numeral 1) cs)

/-- The list of a head and further elements. -/
def listOf (h rs : Term) : Term := nodeT (Term.pair (numeral 2) (consT treeTy h rs))

/-- The atom named by no keyword ({name}`headKeywords`), each test in normal form, in the context
of the further elements and the atom's characters. -/
def atomFreeNf (P : Prog) (K : Kit) : Option (List Term) :=
  headKeywords.mapM fun kw ↦
    nfE K.G K.E (K.rules []) [list treeTy, list treeTy] (unnamed P (atomOf (v 1)) kw)

/-- The name of characters, as the keywords' tests compare it. -/
def nameOfChars (P : Prog) (cs : Term) : Term :=
  nodeT (Term.pair ((nfE P.G #[] (vBase P) [] (numeral 0)).getD (numeral 0)) cs)

/-- The name of a numeral's characters is not the keyword {lit}`kw`: the names' equality, a
bitstring, empty, given that the characters are a numeral's; were it not, by its soundness the
characters would be the keyword's, which are no numeral's. -/
def numeralUnnamed (P : Prog) (S : Defs) (kw : String) : Step :=
  (s!"numeralUnnamed/{kw}", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, (vocab3 ++ ["charsMap"]).filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size⟩
    let childrenT ← primT Kernel.Prim.children
    let Γ := [list treeTy]
    let name (Γ : List Tree) : Term := nameOfChars P (atPos 0 Γ)
    let test (Γ : List Tree) : Term := call D.equal [] [name Γ, pc P kw []]
    let isNum := truth P.o (pc P "Prelude.isSome" [pc P "Reader.numeral" [v 0]])
    let some X := nfE K.G K.E (K.rules []) Γ (test Γ) | none
    let refute : Deducer := linkK K s!"numeralUnnamed {kw}" <|
      K.cutThm "equalSound" (fun Γ ↦ [name Γ]) <| K.allEΓ (fun _ ↦ pc P kw []) <|
      K.impE (K.solve 3) fun Γ Φ ψ ↦
      K.image (Φ.length - 1) (fun t ↦ apps childrenT [t]) (fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ [.delta (P.idx "Reader.numeral")]) .full) 0
          (dFalse K.L dHyp) Γ Φ ψ) Γ Φ ψ
    let some d := decideBits K test (K.solve 3) refute Γ [isNum] (Term.eq X bnilT)
      | dbgTrace s!"numeralUnnamed {kw}: not proved" fun _ ↦ none
    pure (⟨0, Γ, [isNum], Term.eq X bnilT⟩, d))

/-- The soundness at a list of an atom and further elements, in the context of the further
elements and the atom's characters, given that at the atom and at each further element, no
keyword naming the atom, the tests {lit}`kws` ({name}`atomFreeNf`). -/
def appAtomThm (P : Prog) (S : Defs) (T : Defs3) (kws : List Term) : Internal.Thm :=
  ⟨0, [list treeTy, list treeTy],
    [Internal.instTerm [] [atomOf (v 1)] (datatypeφ P S T),
      S.allL (Term.lam treeTy (datatypeφ P S T)) (v 0)] ++ kws,
    Internal.instTerm [] [listOf (atomOf (v 1)) (v 0)] (datatypeφ P S T)⟩

/-- The soundness at a list of an atom and further elements ({name}`appAtomThm`): the
application's at source forms ({name}`appSrc`) at the atom, its head named by no keyword as each
stage reads it, the atom's expansion and erasure the atom; the reader's reading of its erasure
with the numeral abbreviations expanded decided: an abbreviation's numeral atom, by the
abbreviations' coherence, whose characters, a numeral's, are no keyword's; or the atom, its
characters fixed by the expansion, as the list's test of source forms gives. -/
def appAtom (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("appAtom", fun ix E ↦ do
    let K := appKit P S ix E
    let kws ← atomFreeNf P K
    let nK := kws.length
    let W₀ := kwKit P S T ix E 2 (List.replicate (2 + nK) true)
    let W := { W₀ with K := K }
    let L := K.L
    let a := appAtomThm P S T kws
    let unfold := ((List.range nFolds).map T.argIdx ++
      [P.idx "Typing.synList", P.idx "Reader.resolveList"]).map Internal.NormRule.delta
    -- the atom, its characters and the further elements, and the list, in a context
    let cs (Γ : List Tree) : Term := atPos 0 Γ
    let rs (Γ : List Tree) : Term := atPos 1 Γ
    let atom (Γ : List Tree) : Term := atomOf (cs Γ)
    let F (Γ : List Tree) : Term := listOf (atom Γ) (rs Γ)
    let nums (Γ : List Tree) : Term := W.qv 7 Γ
    let expF (Γ : List Tree) : Term := pc P "Datatype.expandExpr" [W.qv 3 Γ, F Γ]
    let fn (Γ : List Tree) : Term :=
      Term.lam treeTy (pc P "Reader.expandNums" [Term.rename (nums Γ) (· + 1), v 0])
    -- a term's equation with its lazy normal form, after the hypotheses
    let cutLazy (t : List Tree → Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
      let (l, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ (t Γ)
      let (r, d) ← lazyNf K.G K.E (K.rules Φ ++ unfold) Γ 64 Φ l
      dCut (Term.eq l r) d k Γ Φ ψ
    -- the atom's name
    let nm (Γ : List Tree) : Term := nameOfChars P (cs Γ)
    -- the application's soundness at source forms at the atom, its antecedents the statement's,
    -- the atom named by no keyword as each stage reads it, by normalization with the stage
    -- functions' steps unfolded
    let app : Deducer :=
      W.cutApply "appSrc" (fun Γ ↦ [rs Γ, atom Γ]) [K.byHyp 0, K.byHyp 1] fun Γ Φ ψ ↦
        dAllE L K.G K.E (Φ.length - 1) (W.qv 1 Γ) (((List.range (nQ - 1)).foldr
          (fun j k ↦ K.allEΓ (W.qv (j + 2)) k) <|
          (List.range W.nH).foldr (fun i k ↦ K.impE (linkK K s!"appAtom: hypothesis {i}"
            (K.byHyp (W.hyp i))) k) <|
          (List.range (srcFree P T).length).foldr (fun j k ↦
            K.impE (linkK K s!"appAtom: keyword {j}" fun Γ Φ ψ ↦
              dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold) .full) (K.solve 3) Γ Φ ψ) k) <|
          linkK K "appAtom: the goal" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ
    -- the atom's name abbreviated: the abbreviation a numeral's atom, by the coherence of the
    -- abbreviations, at the name; no keyword naming it, a numeral's characters being no
    -- keyword's
    let abbreviated : Deducer :=
      linkK K "appAtom: the abbreviation" <|
      dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) (W.hyp 2) fun Γ Φ ψ ↦
      dAllE L K.G K.E (Φ.length - 1) (nm Γ) (K.conjE fun Γ Φ ψ ↦
        let (n₁, n₂) := (Φ.length - 2, Φ.length - 1)
        dImpE L n₂ (K.solve 3) (fun Γ Φ ψ ↦
          dImpE L n₁ (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) (K.exE <| K.conjE fun Γ Φ ψ ↦
            let iNum := Φ.length - 1
            let dsPos := Γ.length - 1
            let ds (Γ : List Tree) : Term := atPos dsPos Γ
            -- the numeral's name named by no reader's keyword, by the lemmas at it
            (readerKeywords.foldr (fun kw k ↦ W.cutApply s!"numeralUnnamed/{kw}"
                (fun Γ ↦ [ds Γ]) [K.byHyp iNum] k) app) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let main : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [nm Γ, nums Γ]])
        app abbreviated
    -- the list's expansion and its presence's test decided, the list's test of source forms;
    -- the atom's characters fixed by the expansion of numeral abbreviations
    let chars : Deducer :=
      cutLazy expF <| fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ (W.hyp 5)) .full) (W.hyp 5) (fun Γ Φ ψ ↦
        K.splitHyp (Φ.length - 1) (cutLazy (fun Γ ↦ pc P "srcForm" [fn Γ,
            pc P "Prelude.get" [expF Γ]]) <|
          decideIn K (fun Γ ↦ pc P "charsFixed" [fn Γ, cs Γ])
            (linkK K "appAtom: the characters not fixed" (K.hypFalse (W.hyp 4))) <|
          K.cutThm "charsFixedEq" (fun Γ ↦ [cs Γ, nums Γ]) <| K.impE (K.solve 3) main)
          6 Γ Φ ψ) Γ Φ ψ
    let _ := (L, rs)
    let some d := (List.range nQ).foldr (fun _ k ↦ dAllI K.L k)
        ((List.range W.nH).foldr (fun _ k ↦ dImpI K.L k) chars) a.ctx a.hyps a.concl
      | dbgTrace "appAtom: not proved" fun _ ↦ none
    pure (a, d))

/-- The arguments of the applications of definitions in a term, outside its binders. -/
def foldedArgs : Term → List Term := RoseTree.para fun l cs ↦ match l with
  | .defn _ _ => cs.map Prod.fst ++ cs.flatMap Prod.snd
  | l => (cs.zipIdx.filter fun (_, i) ↦ Internal.sameCtx l i).flatMap (·.1.2)

/-- The arguments of the applications of the definitions {lit}`ks` in a term, outside its
binders. -/
def foldArgsOf (ks : List ℕ) : Term → List Term := RoseTree.para fun l cs ↦ match l with
  | .defn k _ => (if ks.contains k then cs.map Prod.fst else []) ++ cs.flatMap Prod.snd
  | l => (cs.zipIdx.filter fun (_, i) ↦ Internal.sameCtx l i).flatMap (·.1.2)

/-- A goal proved by normalization with the rules {lit}`rs`, after case analyses, to a depth, of
the datum the weak head normal forms of its sides and of the hypotheses {lit}`hs` gives are blocked
on: a test as a whole, the outermost, by its bits' cases; else the innermost value of a definition
kept folded or of a variable, as a node of a new label and new children; else a list by its
cases; the data the arguments of the definitions {lit}`folds` are blocked on before any other,
the applications of those definitions, which reduce once their arguments are nodes, split only
at variables. The data are read from the normal forms of the depth {lit}`mode`. A
case is also proved where a hypothesis normalizes to falsity, those of {lit}`hs` tried before
each case analysis. -/
def splitSolve (K : Kit) (rs : List Term → List Internal.NormRule) (hs : List Term → List ℕ)
    (depth : ℕ) (folds : List ℕ) (mode : Internal.Depth) : Deducer :=
  let close : Deducer := fun Γ Φ ψ ↦
    (dRwBy (evalRw K.G K.E (rs Φ) .full) (K.solve 3) Γ Φ ψ).orElse fun _ ↦
      (List.range Φ.length).reverse.findSome? fun i ↦
        dRwHyp (evalRw K.G K.E ((rs Φ).filter fun r ↦ match r with
            | .hyp j => j ≠ i
            | _ => true) .full) i (dFalse K.L dHyp) Γ Φ ψ
  -- one of the hypotheses hs gives refuted
  let refuteHs : Deducer := fun Γ Φ ψ ↦ (hs Φ).findSome? fun i ↦
    dRwHyp (evalRw K.G K.E ((rs Φ).filter fun r ↦ match r with
        | .hyp j => j ≠ i
        | _ => true) .full) i (dFalse K.L dHyp) Γ Φ ψ
  Nat.rec (motive := fun _ ↦ Deducer) close (fun _ rec Γ Φ ψ ↦ (refuteHs Γ Φ ψ).orElse fun _ ↦
    let sides := match Internal.eqParts ψ with
      | some (a, b) => [a, b]
      | none => [ψ]
    let whnf (t : Term) : Option Term := (evalRw K.G K.E (rs Φ) mode Γ Φ t).map Prod.fst
    let dataOf (w : Term) : List Term := blocking w ++ match w.label with
      | .var _ => [w]
      | _ => []
    let data (t : Term) : List Term := ((whnf t).map dataOf).getD []
    -- the data the sides and the hypotheses are blocked on, then those the arguments of folded
    -- definitions in them are
    let terms := (sides ++ (hs Φ).filterMap (Φ[·]?)).filterMap whnf
    let blocked := terms.flatMap dataOf ++ (terms.flatMap foldedArgs).flatMap data
    -- an application of a folded definition or of a variable, or a projection of one, whose value
    -- the reduction does not reach; a variable itself is not split
    let stuck (X : Term) : Bool :=
      let t := (List.range 16).foldl (fun (t : Term) _ ↦ match t.label, t.children with
        | .app, f :: _ | .fst, [f] | .snd, [f] => f
        | _, _ => t) X
      match t.label with
      | .defn k _ => !folds.contains k || t.children.all fun c ↦ match c.label with
        | .var _ => true
        | _ => false
      | .var _ => !(match X.label with
        | .var _ => true
        | _ => false)
      | _ => false
    let typed (X : Term) : Option Tree := Internal.typeIn K.G 0 Γ X
    -- a test as a whole, the outermost; else the innermost opaque tree; else a list
    let choose (blocked : List Term) : Option (Term × Tree) :=
      (blocked.find? fun X ↦ typed X = some bitTy ∨ typed X = some bitsTy).orElse
        (fun _ ↦ blocked.reverse.find? fun X ↦ typed X == some treeTy && stuck X) |>.orElse
        (fun _ ↦ blocked.find? fun X ↦ (typed X).any fun ty ↦ ty = list (ty.children.headD ty))
      |>.bind fun X ↦ (typed X).map (X, ·)
    -- the data the arguments of the folds are blocked on first, which decide the tests their
    -- values enter
    let datum := (choose ((terms.flatMap (foldArgsOf folds)).flatMap data)).orElse fun _ ↦
      choose blocked
    match datum with
    | none => (close Γ Φ ψ).orElse fun _ ↦
      dbgTrace s!"splitSolve: a case not closed: {showT ψ}" fun _ ↦ none
    | some (X, ty) =>
      if ty = bitTy then K.bitCase X rec rec Γ Φ ψ
      else if ty = treeTy then K.treeNode X rec Γ Φ ψ
      else K.listCase (ty.children.headD ty) X rec rec Γ Φ ψ) depth

/-- The soundness at a form refuted: the statement's quantifiers and hypotheses introduced, after
the hypotheses before them, the tests of the form's expansion, its typing and its test of source
forms decided until one of them is false ({name}`splitSolve`), with the stage functions' steps
unfolded; the failure traced with a message. -/
def refuteStatement (P : Prog) (S : Defs) (T : Defs3) (K : Kit) (msg : String) : Deducer :=
  fun Γ₀ Φ₀ ψ₀ ↦
    let L := K.L
    let nH := (datatypeParts P S T (v nQ)).1.length
    let unfold := ((List.range nFolds).map T.argIdx ++
      ["Typing.synList", "Reader.resolveList"].map P.idx).map Internal.NormRule.delta
    let hyp (i : ℕ) : ℕ := Φ₀.length + nQ + i
    ((List.range nQ).foldr (fun _ k ↦ dAllI L k)
      ((List.range nH).foldr (fun _ k ↦ dImpI L k)
        (linkK K msg <| dFalse L <| splitSolve K (fun Φ ↦ K.rules Φ ++ unfold)
          (fun _ ↦ [hyp 5, hyp 6, hyp 4]) 24 ((List.range nFolds).map T.foldIdx) .full))) Γ₀ Φ₀ ψ₀

/-- The soundness at a form of a wrong number of elements refuted: the statement's quantifiers and
hypotheses introduced, after the hypotheses before them; each element's expansion, at the
positions {lit}`ps`, decided present, the first first, else the form's absent; all present, the
form's typing absent, with the stage functions' steps unfolded and the further rules
{lit}`extra`, else the tests of the expansion, the typing and the test of source forms decided
({name}`splitSolve`); the failure traced with a message. -/
def refuteForm (P : Prog) (S : Defs) (T : Defs3) (K : Kit) (msg : String) (ps : List ℕ)
    (extra : List Internal.NormRule) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
  let L := K.L
  let nH := (datatypeParts P S T (v nQ)).1.length
  let unfold := ((List.range nFolds).map T.argIdx ++
    ["Typing.synList", "Reader.resolveList"].map P.idx).map Internal.NormRule.delta ++ extra
  let hyp (i : ℕ) : ℕ := Φ₀.length + nQ + i
  let env (Γ : List Tree) : Term := atPos (Γ₀.length - 1 + 3) Γ
  -- a hypothesis refuted with the folds' steps unfolded
  let hypFalseU (h : ℕ) : Deducer := fun Γ Φ ψ ↦
    dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ unfold) .full) h (dFalse K.L dHyp) Γ Φ ψ
  let rest : Deducer := fun Γ Φ ψ ↦ (hypFalseU (hyp 6) Γ Φ ψ).orElse fun _ ↦
    (splitSolve K (fun Φ ↦ K.rules Φ ++ unfold) (fun _ ↦ [hyp 5, hyp 6, hyp 4]) 12
      ((List.range nFolds).map T.foldIdx) .full) Γ Φ ψ
  ((List.range nQ).foldr (fun _ k ↦ dAllI L k)
    ((List.range nH).foldr (fun _ k ↦ dImpI L k)
      (linkK K msg <| dFalse L <| (ps.reverse.foldr (fun p k ↦
        decideOpt K (fun Γ ↦ pc P "Datatype.expandExpr" [env Γ, atPos p Γ])
          (hypFalseU (hyp 5))
          k (minimal := true)) rest)))) Γ₀ Φ₀ ψ₀

/-- The number of variables a node's child of an index binds beyond the node's context. -/
def bindersAt (l : Internal.Label) (i : ℕ) : ℕ := match l with
  | .lam _ => 1
  | .natRec => if i = 1 then 1 else 0
  | .listRec => if i = 1 then 2 else 0
  | .roseRec _ => if i = 0 then 1 else 0
  | _ => 0

/-- A term with each occurrence of the term {lit}`t`, under any binders, replaced by the variable
of index {lit}`x`, both raised under each binder. -/
def abstractUnder (t : Term) (x : ℕ) (u : Term) : Term :=
  RoseTree.para (fun l (cs : List (Term × (ℕ → Term))) (d : ℕ) ↦
    if RoseTree.node l (cs.map Prod.fst) == Term.rename t (· + d) then v (x + d) else
    RoseTree.node l (cs.zipIdx.map fun ((_, r), i) ↦ r (d + bindersAt l i))) u 0

/-- The first fold of lists over the variable of index {lit}`k` in a term, outside its binders. -/
def foldOver (k : ℕ) : Term → Option Term := RoseTree.para fun l cs ↦
  match l, cs.map Prod.fst with
  | .listRec, [_, _, d] =>
    if d == v k then some (RoseTree.node l (cs.map Prod.fst)) else (cs.drop 2).findSome? (·.2)
  | _, _ => (cs.zipIdx.filter fun (_, i) ↦ Internal.sameCtx l i).findSome? (·.1.2)

/-- The helpers of the expansion of a list that the proof that it is a list keeps folded. -/
def expHelpers : List String :=
  ["Datatype.clauseChain", "Datatype.xrAt", "Datatype.xrFrom", "Datatype.clauseCtor",
    "Datatype.bindWith", "Datatype.isData", "Datatype.atomName", "Datatype.isAtomTx",
    "Datatype.namedTx", "Datatype.bindersTx", "Datatype.xrForms", "Datatype.defaultOf",
    "Datatype.expandAliases", "Datatype.cataField", "Datatype.cataRest", "Datatype.caseField",
    "Datatype.caseRest"]

/-- The kit of the proof that the expansion of a list is a list, the expansion's helpers
({name}`expHelpers`) folded. -/
def expKit (P : Prog) (S : Defs) (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
  let K := appKit P S ix E
  { K with P := { P with folded := P.folded ++ expHelpers } }

/-- The expansion of a list, where it is present, a list: its label that of lists, in the
context of the list's elements and the expansion's declarations. -/
def expListThm (P : Prog) : Internal.Thm :=
  let e := pc P "Datatype.expandExpr" [v 1, nodeT (Term.pair (numeral 2) (v 0))]
  ⟨0, [list treeTy, list treeTy], [truth P.o (pc P "Prelude.isSome" [e])],
    Term.eq (call D.lab [] [pc P "Prelude.get" [e]]) (numeral 2)⟩

/-- The expansion of a list ({name}`expListThm`) in weak head normal form, the step of the
expansion's fold at the list taken, with its reduction; the results of the fold at the list's
elements; and the normal form with those results abstracted to the variable of index 0. -/
def expBodyParts (P : Prog) (S : Defs) (T : Defs3) (ix : String → ℕ)
    (E : Array Internal.Entry) : Option (Term × Internal.Deriv × Term × Term) := do
  let K := expKit P S ix E
  let a := expListThm P
  let e := pc P "Datatype.expandExpr" [v 1, nodeT (Term.pair (numeral 2) (v 0))]
  let (w, d) ← evalRw K.G K.E (K.rules [] ++ [.delta (T.argIdx 0)]) .head a.ctx [] e
  let R ← foldOver 0 w
  let B := abstractUnder R 0 w
  if Internal.instTerm [] [R, v 1] B == w then pure (w, d, R, B)
  else dbgTrace "expBody: the results not abstracted" fun _ ↦ none

/-- The expansion of a list at results of its elements' expansions ({name}`expBodyParts`),
where it is present, a list, in the context of the results and the expansion's declarations. -/
def expBodyThm (P : Prog) (S : Defs) (T : Defs3) (ix : String → ℕ) (E : Array Internal.Entry) :
    Option Internal.Thm := do
  let (_, _, R, B) ← expBodyParts P S T ix E
  let ty ← Internal.typeIn P.G 0 (expListThm P).ctx R
  pure ⟨0, [ty, list treeTy], [truth P.o (pc P "Prelude.isSome" [B])],
    Term.eq (call D.lab [] [pc P "Prelude.get" [B]]) (numeral 2)⟩

/-- The expansion of a list at results of its elements' expansions, where it is present, a list
({name}`expBodyThm`): the tests the expansion's reduction is blocked on decided, and the optional
values its cases are blocked on decided nodes, each case a list or absent. -/
def expBody (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("expBody", fun ix E ↦ do
    let K := expKit P S ix E
    let some a := expBodyThm P S T ix E | dbgTrace "expBody: not stated" fun _ ↦ none
    let unfold := (["Datatype.expandCase", "Datatype.expandCata"].map P.idx).map
      Internal.NormRule.delta
    let some d := splitSolve K (fun Φ ↦ K.rules Φ ++ unfold) (fun _ ↦ [0]) 32 [] .head a.ctx a.hyps
        a.concl
      | dbgTrace "expBody: not proved" fun _ ↦ none
    pure (a, d))

/-- The expansion of a list, where it is present, a list ({name}`expListThm`): the expansion
reduced by the step of its fold at the list, an instance of {name}`expBody` at the results of the
fold at the list's elements. -/
def expList (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("expList", fun ix E ↦ do
    let K := expKit P S ix E
    let a := expListThm P
    let e := pc P "Datatype.expandExpr" [v 1, nodeT (Term.pair (numeral 2) (v 0))]
    let some (w, dw, R, _) := expBodyParts P S T ix E | dbgTrace "expList: no parts" fun _ ↦ none
    let some (Internal.Entry.language b) := K.E[K.ix "expBody"]? | none
    let σ := [R, v 1]
    let byEq : Deducer → Deducer := dRwBy (evalRw K.G K.E [.hyp 1] .full)
    let inst : Deducer := fun Γ Φ ψ ↦ do
      let p ← dHyp Γ Φ (Internal.instTerm [] σ (b.hyps.headD Term.star))
      dCut (Internal.instTerm [] σ b.concl) (nd (.apply (K.ix "expBody") [] σ) [p]) dHyp Γ Φ ψ
    let some d := dCut (Term.eq e w) (nd .join [dw, nd .refl])
        (dRwHyp (evalRw K.G K.E [.hyp 1] .full) 0 (byEq inst)) a.ctx a.hyps a.concl
      | dbgTrace "expList: not proved" fun _ ↦ none
    pure (a, d))

/-- A goal about a node whose label the hypothesis of index i gives: the hypothesis renormalized to
the label, the goal normalized with the rules {lit}`rs` and its tests decided ({name}`splitSolve`).
-/
def labelled (K : Kit) (rs : List Term → List Internal.NormRule) (i : ℕ) : Deducer :=
  fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E ((rs Φ).filter fun r ↦ match r with
      | .hyp j => j ≠ i
      | _ => true) .full) i
    (fun Γ Φ ψ ↦ dRwBy (evalRw K.G K.E (rs Φ) .full) (splitSolve K rs (fun _ ↦ []) 16 [] .head)
      Γ Φ ψ)
    Γ Φ ψ

/-- The erasure of the expansion of a list, where it is present, a list, in the context of the
list's elements and the expansion's declarations. -/
def eraseListThm (P : Prog) : Internal.Thm :=
  let e := pc P "Datatype.expandExpr" [v 1, nodeT (Term.pair (numeral 2) (v 0))]
  ⟨0, [list treeTy, list treeTy], [truth P.o (pc P "Prelude.isSome" [e])],
    Term.eq (call D.lab [] [pc P "Datatype.eraseExpr" [pc P "Prelude.get" [e]]]) (numeral 2)⟩

/-- The erasure of the expansion of a list, where it is present, a list ({name}`eraseListThm`):
the expansion a list ({name}`expList`), a node of that label; the erasure's step unfolded, the
tests of its reduction decided ({name}`splitSolve`). -/
def eraseList (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("eraseList", fun ix E ↦ do
    let K := appKit P S ix E
    let a := eraseListThm P
    let rs (Φ : List Term) := K.rules Φ ++ [.delta (T.argIdx 2)]
    let e := pc P "Datatype.expandExpr" [v 1, nodeT (Term.pair (numeral 2) (v 0))]
    let some (Internal.Entry.language b) := K.E[K.ix "expList"]? | none
    let σ := [v 0, v 1]
    let some (X, _) := evalRw K.G K.E (rs []) .full a.ctx [] (pc P "Prelude.get" [e]) | none
    -- hypotheses: the expansion's presence, its label, its node, its label renormalized
    let some d := (fun Γ Φ ψ ↦ do
        let p ← dHyp Γ Φ (Internal.instTerm [] σ (b.hyps.headD Term.star))
        dCut (Internal.instTerm [] σ b.concl) (nd (.apply (K.ix "expList") [] σ) [p])
          (K.treeNode X (labelled K rs 1)) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "eraseList: not proved" fun _ ↦ none
    pure (a, d))

/-- A list's numeral abbreviations expanded, a list, in the context of the list and the
abbreviations. -/
def numsListThm (P : Prog) : Internal.Thm :=
  ⟨0, [treeTy, list treeTy], [Term.eq (call D.lab [] [v 0]) (numeral 2)],
    Term.eq (call D.lab [] [pc P "Reader.expandNums" [v 1, v 0]]) (numeral 2)⟩

/-- No keyword {lit}`kw` names a list, in the context of the list. -/
def namedListThm (P : Prog) (kw : String) : Internal.Thm :=
  ⟨0, [treeTy], [Term.eq (call D.lab [] [v 0]) (numeral 2)], unnamed P (v 0) kw⟩

/-- A lemma about a tree of a given label, the variable of index 0: the tree a node, its label
renormalized, the goal by normalization and case analyses ({name}`labelled`). -/
def labelStep (P : Prog) (S : Defs) (name : String) (a : Internal.Thm) (folds : List ℕ) : Step :=
  (name, fun ix E ↦ do
    let K := appKit P S ix E
    let rs (Φ : List Term) := K.rules Φ ++ folds.map Internal.NormRule.delta
    let some d := K.treeNode (v 0) (fun Γ Φ ψ ↦ labelled K rs 0 Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The name of the lemma that no keyword {lit}`kw` names a list. -/
def namedListName (kw : String) : String := s!"namedList/{kw}"

/-- The lemmas that the erasure of the expansion of a list and that erasure with its numeral
abbreviations expanded are lists, and that no keyword the erasure or the reader reads names a
list. -/
def viewsUnnamed (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [eraseList P S T, labelStep P S "numsList" (numsListThm P) [T.argIdx 3]] ++
    (erasureKeywords ++ readerKeywords).eraseDups.map fun kw ↦
      labelStep P S (namedListName kw) (namedListThm P kw) []

/-- The soundness at a list of a list and further elements, in the context of the further
elements and the head's elements, given that at the head and at each further element. -/
def appListThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  let hd := nodeT (Term.pair (numeral 2) (v 1))
  ⟨0, [list treeTy, list treeTy],
    [Internal.instTerm [] [hd] (datatypeφ P S T),
      S.allL (Term.lam treeTy (datatypeφ P S T)) (v 0)],
    Internal.instTerm [] [listOf hd (v 0)] (datatypeφ P S T)⟩

/-- The soundness at a list of a list and further elements ({name}`appListThm`): the head's
expansion present, else the list's absent; the head's expansion a list ({name}`expList`), its
label decided; the application's soundness at source forms ({name}`appSrc`) at the head, no
keyword naming the head or its expansion as each stage reads them, each by normalization with the
stage functions' steps unfolded and the tests their reductions are blocked on decided. -/
def appList (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("appList", fun ix E ↦ do
    let K := appKit P S ix E
    let W₀ := kwKit P S T ix E 2 [true, true]
    let W := { W₀ with K := K }
    let L := K.L
    let a := appListThm P S T
    -- the steps of the folds; past the facts of the head's form, all but the expansion's, which
    -- the head's generalized expansion replaces
    let unfold (j : ℕ) := ((List.range nFolds).filter (j < 2 ∨ 0 < ·)).map fun k ↦
      Internal.NormRule.delta (T.argIdx k)
    let hcs (Γ : List Tree) : Term := atPos 0 Γ
    let rs (Γ : List Tree) : Term := atPos 1 Γ
    let hd (Γ : List Tree) : Term := nodeT (Term.pair (numeral 2) (hcs Γ))
    let expH (Γ : List Tree) : Term := pc P "Datatype.expandExpr" [W.qv 3 Γ, hd Γ]
    let last : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let renormLast (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1)) .full) (Φ.length - 1) k Γ Φ ψ
    -- no keyword naming the head or its expansion: as the typing reads them, by normalization
    -- and case analyses; as the erasure and the reader read the expansion, the views lists
    -- ({name}`viewsUnnamed`)
    let fact (j : ℕ) : Deducer := fun Γ Φ ψ ↦
      let nT := 3 + typingKeywords.length
      if j < nT then
        dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold j) .full)
          (splitSolve K (fun Φ ↦ K.rules Φ ++ unfold j) (fun _ ↦ []) 12 [] .head) Γ Φ ψ
      else do
        let eras := j < nT + erasureKeywords.length
        let kw := if eras then erasureKeywords.getD (j - nT) ""
          else readerKeywords.getD (j - nT - erasureKeywords.length) ""
        let g := pc P "Datatype.eraseExpr" [pc P "Prelude.get" [expH Γ]]
        let nf (t : Term) : Option Term := (evalRw K.G K.E (K.rules Φ) .full Γ Φ t).map Prod.fst
        let some (view, nums) := (if eras then [(g, g)] else
            (List.range Γ.length).map fun i ↦ (pc P "Reader.expandNums" [v i, g], v i)).find?
              fun (y, _) ↦ nf (unnamed P y kw) == nf ψ
          | dbgTrace s!"appList: fact {j} not a view's" fun _ ↦ none
        -- the erasure a list, the view a list, no keyword naming it, that renormalized
        let numsSteps : Deducer → Deducer := if eras then id else
          W.cutApply "numsList" (fun _ ↦ [g, nums]) [dHyp]
        W.cutApply "eraseList" (fun Γ ↦ [hcs Γ, W.qv 3 Γ]) [K.solve 3]
          (numsSteps (W.cutApply (namedListName kw) (fun _ ↦ [view]) [dHyp]
            (renormLast (K.solve 3)))) Γ Φ ψ
    -- the application's soundness at the head, its antecedents the statement's, no keyword
    -- naming the head or its expansion
    let app : Deducer :=
      W.cutApply "appSrc" (fun Γ ↦ [rs Γ, hd Γ]) [K.byHyp 0, K.byHyp 1] fun Γ Φ ψ ↦
        dAllE L K.G K.E (Φ.length - 1) (W.qv 1 Γ) (((List.range (nQ - 1)).foldr
          (fun j k ↦ K.allEΓ (W.qv (j + 2)) k) <|
          (List.range W.nH).foldr (fun i k ↦ K.impE (linkK K s!"appList: hypothesis {i}"
            (K.byHyp (W.hyp i))) k) <|
          (List.range (srcFree P T).length).foldr (fun j k ↦
            K.impE (linkK K s!"appList: keyword {j}" (fact j)) k) <|
          linkK K "appList: the goal" last)) Γ Φ ψ
    -- the head's expansion present, a list, generalized and decided a node of that label
    let present : Deducer :=
      W.generalize (fun Γ ↦ pc P "Prelude.get" [expH Γ]) fun Γ₀ Φ₀ ψ₀ ↦
        let h' (Γ : List Tree) : Term := atPos (Γ₀.length - 1) Γ
        (W.cutApply "expList" (fun Γ ↦ [hcs Γ, W.qv 3 Γ]) [K.solve 3] <| renormLast <|
          fun Γ Φ ψ ↦
            -- the expansion's label, renormalized once the expansion is a node
            let iLab := Φ.length - 1
            K.treeNode (h' Γ) (fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ iLab) .full) iLab app Γ Φ ψ) Γ Φ ψ) Γ₀ Φ₀ ψ₀
    let decisions : Deducer :=
      decideOpt K expH (linkK K "appList: the head's expansion absent" <|
          W.cutApply "expHead" (fun Γ ↦ [rs Γ, hcs Γ, W.qv 3 Γ])
            [fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦ K.solve 3 Γ Φ ψ]
            fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)
        present (minimal := true)
    let some d := (List.range nQ).foldr (fun _ k ↦ dAllI K.L k)
        ((List.range W.nH).foldr (fun _ k ↦ dImpI K.L k) decisions) a.ctx a.hyps a.concl
      | dbgTrace "appList: not proved" fun _ ↦ none
    pure (a, d))

/-- The expansion of a list headed by a list, where it is present, has its head's present, in the
context of the further elements, the head's elements and the expansion's declarations. -/
def expHeadThm (P : Prog) : Internal.Thm :=
  let isSome (t : Term) : Term := truth P.o (pc P "Prelude.isSome" [t])
  let hd := nodeT (Term.pair (numeral 2) (v 1))
  ⟨0, [list treeTy, list treeTy, list treeTy],
    [isSome (pc P "Datatype.expandExpr" [v 2, listOf hd (v 0)])],
    isSome (pc P "Datatype.expandExpr" [v 2, hd])⟩

/-- The expansion of a list headed by a list, where it is present, has its head's present
({name}`expHeadThm`): the tests of both expansions and their optional values decided
({name}`splitSolve`), the fold of the expansion unfolded at nodes by the vocabulary's equations,
the gathering of the elements' expansions ({lit}`Datatype.xrFrom`) and the tests of a list's head
unfolded. -/
def expHead (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("expHead", fun ix E ↦ do
    let K₀ := appKit P S ix E
    let open_ := ["Datatype.xrFrom", "Datatype.namedTx", "Datatype.nthTx", "Datatype.xrForms"]
    let K := { K₀ with P := { P with folded := P.folded ++ expHelpers.filter (!open_.contains ·) } }
    let a := expHeadThm P
    let some d := splitSolve K (fun Φ ↦ K.rules Φ ++ [.delta (T.argIdx 0)]) (fun _ ↦ [0]) 32 []
        .head a.ctx a.hyps a.concl
      | dbgTrace "expHead: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the expansion of a list: at results of its elements' expansions, and at
the list. -/
def expansionDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [expBody P S T, expList P S T, expHead P S T]

/-- The development of the expansion of a list ({name}`expansionDev3`), after the base's, the
atom's, the list's, the stage functions' at applications and the applications', stored as the
certificate {lit}`datatype-expansion`. -/
def expansionCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (stagesDev3 P S T).map (·.1) ++ (applyDev3 P S T).map (·.1))
    "datatype-expansion" (expansionDev3 P S T) before

/-- The development of the soundness at lists. -/
def assemblyDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  readerKeywords.map (numeralUnnamed P S) ++ [appAtom P S T] ++ viewsUnnamed P S T ++
    [appList P S T]

/-- The development of the soundness at lists ({name}`assemblyDev3`), after the base's, the
atom's, the list's, the stage functions' at applications, the applications' and the list
expansion's, stored as the certificate {lit}`datatype-assembly`. -/
def assemblyCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (stagesDev3 P S T).map (·.1) ++ (applyDev3 P S T).map (·.1) ++
    (expansionDev3 P S T).map (·.1)) "datatype-assembly" (assemblyDev3 P S T) before

/-- The name of the soundness at the lists headed by the keyword {lit}`kw`. -/
def kwListName (kw : String) : String := s!"kwList/{kw}"

/-- The soundness at a list headed by the keyword {lit}`kw`, in the context of its further
elements, given that at each further element. -/
def kwListThm (P : Prog) (S : Defs) (T : Defs3) (kw : String) : Internal.Thm :=
  ⟨0, [list treeTy], [S.allL (Term.lam treeTy (datatypeφ P S T)) (v 0)],
    Internal.instTerm [] [listOf (kwAtom P kw) (v 0)] (datatypeφ P S T)⟩

end GebTests.Prototypes.FreeTopos.Datatypes

end
