/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeCataCore
public meta import GebTests.Prototypes.FreeTopos.DatatypeCataCore -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at a structural recursion's source form

The soundness of the datatype language's stage-1 compiler at a list headed by the keyword of
structural recursions: the metadata of its clauses shaped as its expansion writes them, whose flags
are a numeral's atom since the equality of trees takes the values zero and one, and the soundness
at its expanded form.

## Main definitions

* {lit}`cataSrcCertificates` — the development, stored as the certificate
  {lit}`datatype-cata-src`.

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

/-- The equality of trees of a tree with itself the numeral one: of bitstrings, by induction on the
bitstring, its bits split; elementwise of a list with itself, given each element's, by induction on
the list; the induction hypothesis on rose trees as every child's; of trees, by induction on the
tree; and at trees it holds of, by its soundness ({lit}`equalSound`). -/
def equalOneLemmas (P : Prog) (S : Defs) : List Step :=
  let kit (ix : String → ℕ) (E : Array Internal.Entry) : Kit := ⟨P, S, E, ix, []⟩
  let oneφ : Term := Term.eq (call D.equal [] [v 0, v 0]) (numeral 1)
  [("eqBOne", fun ix E ↦ do
      let K := kit ix E
      let φ := Term.eq (call D.eqB [] [v 0, v 0]) (numeral 1)
      let d₀ ← K.solve 2 [] [] (Term.subst φ (Internal.instVar (Term.arr 0 [bitTy] Term.star)))
      let byIH : Deducer := normHyps K [0] (K.solve 2)
      let cons : Deducer := fun Γ Φ ψ ↦ (K.bitCase (v 0) byIH byIH Γ Φ ψ).orElse fun _ ↦
        K.bitCase (v 1) byIH byIH Γ Φ ψ
      let d₁ ← cons [list bitTy, bitTy] [Internal.weakenElem φ] (Internal.listConsAt 1 bitTy φ)
      pure (⟨0, [bitsTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁])),
    ("allZipOne", fun ix E ↦ do
      let K := kit ix E
      let L := K.L
      let φ := Internal.Logic.imp P.o (S.allL (Term.lam treeTy oneφ) (v 0))
        (Term.eq (call D.allZip [] [← mapEq (v 0), v 0]) (numeral 1))
      let d₀ ← dImpI L (K.solve 2) [] [] (Term.subst φ (Internal.instVar
        (Term.arr 0 [treeTy] Term.star)))
      -- a construction: the head's equation and the rest's hypothesis, from the hypothesis on all
      -- the elements; the rest's equation by the induction hypothesis
      let cons : Deducer := dImpI L fun Γ₁ Φ₁ ψ₁ ↦
        let h := Φ₁.length - 1
        dRwHyp (evalRw K.G K.E (K.rules Φ₁) .full) h (K.conjE fun Γ Φ ψ ↦
          dImpE L 0 (K.byHyp (Φ.length - 1)) (fun Γ Φ ψ ↦
            normHyps K [Φ.length - 1] (K.solve 2) Γ Φ ψ) Γ Φ ψ) Γ₁ Φ₁ ψ₁
      let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ]
        (Internal.listConsAt 1 treeTy φ)
      pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁])),
    roseAllFor P S "roseAllOne" oneφ fun K h ↦ normHyps K [h] (K.solve 2),
    ("equalOne", fun ix E ↦ do
      let K := kit ix E
      let withLast (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
      -- context: the children, the label
      let node : Deducer := fun Γ Φ ψ ↦
        let l := v (Γ.length - 1)
        let cs (Γ : List Tree) : Term := v (Γ.length - 2)
        K.cutThm "eqBOne" (fun _ ↦ [l]) (withLast fun hl ↦
          K.cutThm "roseAllOne" (fun Γ ↦ [cs Γ]) (K.impE dHyp (withLast fun all ↦
            K.cutThm "allZipOne" (fun Γ ↦ [cs Γ])
              (K.impE (fun _ _ _ ↦ some (nd (.hyp all))) (withLast fun hz ↦
                normHyps K [hl, hz] (K.solve 2)))))) Γ Φ ψ
      let d ← node [list treeTy, bitsTy] [Internal.roseHyp 0 1 oneφ]
        (Internal.roseNodeAt 2 treeTy bitsTy oneφ)
      pure (⟨0, [treeTy], [], oneφ⟩, nd (.roseIndHyp 2 0 1) [d])),
    ("equalOneOf", fun ix E ↦ do
      let K := kit ix E
      let a : Internal.Thm := ⟨0, [treeTy, treeTy], [K.truthB (call D.equal [] [v 1, v 0])],
        Term.eq (call D.equal [] [v 1, v 0]) (numeral 1)⟩
      let d ← K.cutThm "equalSound" (fun _ ↦ [v 1]) (K.allEΓ (fun _ ↦ v 0)
        (K.impE (K.byHyp 0) (K.cutThm "equalOne" (fun _ ↦ [v 0]) fun Γ Φ ψ ↦
          normHyps K [Φ.length - 2, Φ.length - 1] (K.solve 2) Γ Φ ψ)))
        a.ctx a.hyps a.concl
      pure (a, d))]

/-- A name test's value at a tree and a name is a flag, its atom the numeral's the expansion writes:
the tree an atom or not, the equality of names decided; at names it holds of, the numeral one
({name}`equalOneLemmas`). In the context of the tree and the name. -/
def namedFlag (P : Prog) (S : Defs) : Step :=
  ("namedFlag", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let equalT ← primT Kernel.Prim.equal
    let name (Γ : List Tree) : Term := pc P "Reader.nameOf" [atPos 0 Γ]
    let a : Internal.Thm := ⟨0, [treeTy, treeTy], [],
      flagOk P (pc P "Datatype.numAtom" [pc P "Reader.named" [v 1, v 0]])⟩
    let some d := decideIn K (fun Γ ↦ pc P "Reader.isAtom" [atPos 0 Γ]) (K.solve 3)
        (decideIn K (fun Γ ↦ apps equalT [name Γ, atPos 1 Γ]) (K.solve 3)
          (applyThm K "equalOneOf" (fun Γ ↦ [atPos 1 Γ, name Γ]) [K.solve 3] fun Γ Φ ψ ↦
            normHyps K [Φ.length - 1] (K.solve 3) Γ Φ ψ))
        a.ctx a.hyps a.concl
      | dbgTrace "namedFlag: not proved" fun _ ↦ none
    pure (a, d))

/-- A predicate {lit}`pr` holds of each value of a function {lit}`entry` of two trees. -/
def entryAll (P : Prog) (pr entry : Term) : Term :=
  let all := Internal.Logic.all P.o
  all treeTy (Term.lam treeTy (all treeTy (Term.lam treeTy
    (Term.app (sh 2 pr) (Term.app (Term.app (sh 2 entry) (v 1)) (v 0))))))

/-- A predicate of each value of the function of the entries holds of each entry of the variables'
split at the fields' types ({lit}`splitVars`), the entries of both lists being its values: by
induction on the variables, the fields' types split at a construction. In the context of the
variables, the remaining children's type, the function of the entries and the predicate. -/
def splitEntries (P : Prog) (S : Defs) : Step :=
  ("splitEntries", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, walkRules ix E ++ ["splitRebuild"]⟩
    let L := K.L
    let (o, conj) := (P.o, Internal.Logic.conj P.o)
    let sv := pc P "Datatype.splitVars" [v 0, v 2, v 1, v 3]
    let φ := Internal.Logic.imp o (entryAll P (v 3) (v 2)) (Internal.Logic.all o (list treeTy)
      (Term.lam (list treeTy) (conj (S.allL (v 4) (Term.fst sv)) (S.allL (v 4) (Term.snd sv)))))
    let Γ := [list treeTy, treeTy, exp treeTy (exp treeTy treeTy), exp treeTy omega]
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    let conjs : ℕ → Deducer := fun n ↦ n.rec anyHyp fun _ rec ↦ K.norm fun Γ Φ ψ ↦
      (anyHyp Γ Φ ψ).orElse fun _ ↦ dConjI L rec rec Γ Φ ψ
    let d₀ ← dImpI L (dAllI L (K.solve 3)) Γ.tail [] (Term.subst φ (Internal.instVar (nilT treeTy)))
    -- a construction: positions the variable 3, the rest 4, the fields' types 5; at a construction
    -- of them, its head 6 and tail 7; the rest's split at the types remaining, with the entry at
    -- the variable and the type its field takes
    let at_ (iAll : ℕ) (rest : List Tree → Term) (ty : List Tree → Term) : Deducer :=
      fun Γ Φ ψ ↦ dAllE L K.G K.E iAll (rest Γ) (K.conjE fun Γ Φ ψ ↦
        dAllE L K.G K.E 1 (atPos 3 Γ) (K.allEΓ ty (conjs 4)) Γ Φ ψ) Γ Φ ψ
    let cons : Deducer := dImpI L <| dImpE L 0 (K.byHyp 1) fun Γ Φ ψ ↦
      let iAll := Φ.length - 1
      dAllI L (K.listCase treeTy (v 0) (at_ iAll (fun _ ↦ nilT treeTy) (atPos 2))
        (at_ iAll (atPos 7) (atPos 6))) Γ Φ ψ
    let some d₁ := cons (list treeTy :: treeTy :: Γ.tail) [Internal.weakenElem φ]
        (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "splitEntries: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The program with a clause's constructor and the variables' split kept folded, in which the
metadata of a structural recursion's clauses are found. -/
def splitFolded (P : Prog) : Prog := { P with folded := P.folded ++ ["Datatype.splitVars"] }

/-- The hypotheses of a structural recursion's clauses' parts: their entry v0 a flag's and without
a third element at each of its values. -/
def cataPartsHyps (P : Prog) : List Term :=
  [entryAll P (flagEntry P) (v 0), entryAll P (shapeEntry P) (v 0)]

/-- The arguments of a call of the definition of index k at four arguments. -/
def call4 (k : ℕ) (t : Term) : Option (List Term) := do
  let (f, x₄) ← match t.label, t.children with
    | .app, [f, x] => some (f, x)
    | _, _ => none
  let (f, x₃) ← match f.label, f.children with
    | .app, [f, x] => some (f, x)
    | _, _ => none
  let (f, x₂) ← match f.label, f.children with
    | .app, [f, x] => some (f, x)
    | _, _ => none
  let (f, x₁) ← match f.label, f.children with
    | .app, [f, x] => some (f, x)
    | _, _ => none
  match f.label with
  | .defn j _ => if j == k then some [x₁, x₂, x₃, x₄] else none
  | _ => none

set_option linter.unusedVariables false in
/-- The metadata's function of the clauses' parts ({name}`metaFun`) satisfies the hypothesis of
{lit}`cataMetasShaped` at a structural recursion's shape ({name}`cataShape`), in the parts' context:
the presence at a clause split at the tests it is blocked on, each false case refuting it; the
entries' predicates by {name}`splitEntries`. -/
def cataMetaStep (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cataMetaStep", fun ix E ↦ do
    let W := kwKit (ctorFolded (splitFolded P)) S T ix E 1 [true]
    let K := W.K
    let L := K.L
    let P := K.P
    let some f := metaFun K | dbgTrace "cataMetaStep: no metadata function" fun _ ↦ none
    let a : Internal.Thm := ⟨0, partsCtx, cataPartsHyps P, metaEachAt P (cataShape P S) f⟩
    let sv := P.idx "Datatype.splitVars"
    -- the predicate of index i of the entries, at the split the goal mentions
    let byEntries : Deducer := fun Γ Φ ψ ↦ do
      let some (t, 0) := findUnder (fun t ↦ (call4 sv t).isSome) ψ 0 | none
      let args ← call4 sv t
      let (fts, w, vars, entry) := (args.getD 0 Term.star, args.getD 1 Term.star,
        args.getD 2 Term.star, args.getD 3 Term.star)
      [(flagEntry P, 0), (shapeEntry P, 1)].findSome? fun (pr, i) ↦
        K.cutThm "splitEntries" (fun _ ↦ [vars, w, entry, pr]) (K.impE (K.byHyp i)
          (K.allEΓ (fun _ ↦ fts) (K.conjE fun Γ Φ ψ ↦
            (K.byHyp (Φ.length - 1) Γ Φ ψ).orElse fun _ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ))) Γ Φ ψ
    let goal : ℕ → Deducer := fun n ↦ n.rec (fun _ _ _ ↦ none) fun _ rec ↦ K.norm fun Γ Φ ψ ↦
      if ψ == Internal.Logic.tt P.o then some Internal.Logic.trueI else
      match defnParts ψ with
      | some (i, _, _) => if i = P.o + 1 then dConjI L rec rec Γ Φ ψ else byEntries Γ Φ ψ
      | none => (K.byNorm Γ Φ ψ).orElse fun _ ↦ byEntries Γ Φ ψ
    let some d := (dAllI L <| dImpI L <| fun Γ Φ ψ ↦
        K.splitHyp (Φ.length - 1) (linkK K "cataMetaStep: a case" (goal 8)) 14 Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "cataMetaStep: not proved" fun _ ↦ none
    pure (a, d))

/-- The clauses' parts of a structural recursion, present, their metadata shaped
({name}`partsOkWith`). -/
def cataPartsOk (P : Prog) (S : Defs) (T : Defs3) : Step :=
  partsOkWith "cataPartsOk" "cataMetaStep" "cataMetasShaped" (fun _ ↦ v 0) partsCtx
    (fun P ↦ cataShape P S) cataPartsHyps (splitFolded P) S T

/-- The development of the metadata of a structural recursion's clauses, shaped. -/
def cataShapeDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  ltSuccs P [4] 6 ++ equalOneLemmas P S ++ [namedFlag P S,
    lcaseRebuild P S "splitRebuild" treeTy (prod (list treeTy) (list treeTy)), splitEntries P S,
    metasShapedWith "cataMetasShaped" (fun P ↦ cataShape P S) P S T, cataMetaStep P S T,
    cataPartsOk P S T]

/-- The statement of the soundness at a structural recursion at source forms: in the context of the
elements after the keyword, given the soundness at each and at each one's children, the soundness at
the list the keyword heads ({lit}`headedφ` without its quantifier). -/
def cataSrcThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  ⟨0, [list treeTy], [S.allL (Term.lam treeTy (datatypeφ P S T)) (v 0), childrenφ P S T],
    Internal.instTerm [] [listOf (kwAtom P "Datatype.kwCata") (v 0)] (datatypeφ P S T)⟩

set_option linter.unusedVariables false in
/-- The soundness at a structural recursion at source forms ({name}`cataSrcThm`). -/
def cataSrc (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cataSrc", fun ix E ↦ do
    let Pc : Prog := { chainProg P with
      folded := (chainProg P).folded ++ ["Datatype.clauseParts"] }
    let W₀ := kwKit Pc S T ix E 1 [true, true] "Datatype.kwCata"
    let extra := (lenRules ++ ["ltSucc4", "rebXR"]).filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size
    let W : KwKit :=
      { W₀ with K := { W₀.K with more := (W₀.K.more ++ walkRules ix E ++ extra).eraseDups } }
    let K := W.K
    let L := K.L
    let P := K.P
    -- the kit with the expansion of structural recursions unfolded, in which the statement's
    -- expansion and the expanded form's agree
    let Ku : Kit := { K with P := { K.P with
      folded := K.P.folded.filter (· != "Datatype.expandCata") } }
    let a := cataSrcThm P S T
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    -- the hypothesis on the elements split at the three before the clauses
    let splitHypAt (h : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h (K.conjE <| K.conjE <| K.conjE k) Γ Φ ψ
    -- the main case, the elements the datatype's atom 1, the result type 3, the scrutinee 5, a
    -- clause 7 and the further clauses 8, the scrutinee's expansion the last variable, the
    -- expansion's presence the hypothesis hE: the atom and the datatype decided; the clauses'
    -- parts q decided present; their facts (cataPartsOk); the scrutinee sound at expanded forms
    -- (expSound), the bodies (bodiesSound); cataCore at the parts, instantiated at the statement's
    -- variables, its hypotheses the statement's
    let main (W : KwKit) (hE : ℕ) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦ do
      let pS := Γ₀.length - 1
      let up (t : Term) (Γ : List Tree) : Term := Term.rename t (· + (Γ.length - Γ₀.length))
      -- the elements' forms as the expansion's fold rebuilds them, which its parts read
      let form (c : ℕ) (Γ : List Tree) : Term :=
        Term.fst (Term.app (Term.snd (T.foldAt 0 [] (atPos c Γ))) Term.star)
      let dAtom : List Tree → Term := form 1
      let isD (Γ : List Tree) : Term := pc P "Prelude.and" [pc P "Datatype.isAtomTx" [dAtom Γ],
        pc P "Datatype.isData" [pc P "Datatype.atomName" [dAtom Γ], W.qv 3 Γ]]
      let absent : Deducer := linkK K "cataSrc: the datatype absent" fun Γ Φ ψ ↦
        (K.hypFalse hE Γ Φ ψ).orElse fun _ ↦ W.hypFalseU hE Γ Φ ψ
      let rest (Γ : List Tree) : Term := consT treeTy (atPos 7 Γ) (atPos 8 Γ)
      let afterData : Deducer := fun Γ₁ Φ₁ ψ₁ ↦ do
        let (t, _) ← evalRw K.G K.E (K.rules Φ₁) .full Γ₁ Φ₁ (← Φ₁[hE]?)
        let some (q₁, 0) := findUnder
            (fun t ↦ (call5 (P.idx "Datatype.clauseParts") t).isSome) t 0
          | dbgTrace "cataSrc: no parts" fun _ ↦ none
        let args₁ ← call5 (P.idx "Datatype.clauseParts") q₁
        let up₁ (t : Term) (Γ : List Tree) : Term := Term.rename t (· + (Γ.length - Γ₁.length))
        let q (Γ : List Tree) : Term := up₁ q₁ Γ
        let entry (Γ : List Tree) : Term := up₁ (args₁.getD 4 Term.star) Γ
        -- the entry's hypotheses: a flag's by the name test's flag, the third element absent
        let hFlag : Deducer := linkK K "cataSrc: the entries' flags" <|
          dAllI L <| dAllI L fun Γ Φ ψ ↦
            K.cutThm "namedFlag" (fun Γ ↦ [pc P "Datatype.atomName" [dAtom Γ], v 0]) (fun Γ Φ ψ ↦
              K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
        let hShape : Deducer := linkK K "cataSrc: the entries' shapes" <|
          dAllI L <| dAllI L <| K.norm <| dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
        let cataCoreAt : Deducer := fun Γ Φ ψ ↦
          -- after the parts' conjunctions (shapes, bodies' equation), expSound's three steps and
          -- bodiesSound's four
          let (iExp, iBodies, iShape) := (Φ.length - 5, Φ.length - 1, Φ.length - 9)
          (applyThm K "cataCore" (fun Γ ↦ [Term.snd (Term.snd (Term.snd (q Γ))),
              Term.fst (Term.snd (Term.snd (q Γ))),
              pc P "Datatype.defaultOf" [pc P "Datatype.expandAliases" [W.qv 3 Γ, form 3 Γ]],
              atPos pS Γ, form 3 Γ, Term.fst (Term.snd (q Γ))])
            [linkK K "cataSrc: the scrutinee" (K.byHyp iExp),
              linkK K "cataSrc: the bodies" (K.byHyp iBodies),
              linkK K "cataSrc: the shapes" (K.byHyp iShape)] <|
          linkK K "cataSrc: the instance" fun Γ Φ ψ ↦
            dAllE L K.G K.E (Φ.length - 1) (W.qv 1 Γ) (((List.range (nQ - 1)).foldr
              (fun j k ↦ K.allEΓ (W.qv (j + 2)) k) <|
              (List.range W.nH).foldr (fun i k ↦ K.impE (linkK K s!"cataSrc: hypothesis {i}"
                (byStatement Ku (W.hyp i))) k) fun Γ Φ ψ ↦ Ku.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ)
            Γ Φ ψ
        (decideIn K (fun Γ ↦ Term.fst (q Γ))
            (linkK K "cataSrc: the parts absent" fun Γ Φ ψ ↦
              (K.hypFalse hE Γ Φ ψ).orElse fun _ ↦ W.hypFalseU hE Γ Φ ψ) <|
          applyThm K "cataPartsOk" (fun Γ ↦ (args₁.map (up₁ · Γ)).reverse)
            [linkK K "cataSrc: the parts present" (K.solve 3), hFlag, hShape] <|
          K.conjE <| K.conjE <| K.conjE <|
          W.cutApply "expSound" (fun Γ ↦ [atPos 5 Γ])
            [linkK K "cataSrc: the scrutinee's soundness" anyHyp] <|
          K.allEΓ (W.qv 3) <| K.impE (linkK K "cataSrc: the scrutinee present" (K.solve 3)) <|
          K.cutThm "bodiesSound" (fun Γ ↦ [rest Γ, W.qv 3 Γ]) <|
          K.impE (linkK K "cataSrc: the clauses' children" anyHyp) <|
          K.impE (linkK K "cataSrc: the clauses' expansions" anyHyp) <|
          K.impE (linkK K "cataSrc: the clauses' lengths" anyHyp) cataCoreAt) Γ₁ Φ₁ ψ₁
      (splitHypAt 0 <| splitHypAt 1 <| decideIn K isD absent afterData) Γ₀ Φ₀ ψ₀
    -- the statement at a list of at least four elements after the keyword, its kit at the context
    -- reached: the quantifiers and hypotheses introduced; the steps unfolded; the expansion of
    -- structural recursions unfolded in the expansion's presence; the scrutinee's expansion decided
    -- present
    let mk (n h : ℕ) : KwKit :=
      { kwKit Pc S T ix E n (List.replicate h true) "Datatype.kwCata" with K := K }
    let mainBranch : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let W := mk Γ₀.length Φ₀.length
      ((List.range nQ).foldr (fun _ k ↦ dAllI L k) <| (List.range W.nH).foldr
        (fun _ k ↦ dImpI L k) <|
        W.unfold (fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ (W.hyp 5) ++
            [.delta (P.idx "Datatype.expandCata")]) .full) (W.hyp 5) (fun Γ Φ ψ ↦
            let hE := Φ.length - 1
            (W.presentAt "the scrutinee's expansion" (fun Γ ↦
                pc P "Datatype.expandExpr" [W.qv 3 Γ, atPos 5 Γ]) hE (W.hyp 5)
              (main W hE) (unfolding := false)) Γ Φ ψ) Γ Φ ψ) 1) Γ₀ Φ₀ ψ₀
    let refute (msg : String) (ps : List ℕ) : Deducer :=
      srcShort Pc "Datatype.kwCata" K Ku S T msg ps
    let some d := K.listCase treeTy (v 0) (refute "no elements" [])
        (K.listCase treeTy (v 0) (refute "one element" [1])
          (K.listCase treeTy (v 0) (refute "two elements" [1, 3])
            (K.listCase treeTy (v 0) (refute "three elements" [1, 3, 5]) mainBranch)))
        a.ctx a.hyps a.concl
      | dbgTrace "cataSrc: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at every list headed by the keyword of structural recursions ({lit}`headedφ`),
from that at source forms ({name}`cataSrc`): its quantifier and hypotheses introduced. -/
def cataHeaded (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cataHeaded", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let φ := headedφ P S T "Datatype.kwCata"
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    let some d := (dAllI K.L <| dImpI K.L <| dImpI K.L <|
        applyThm K "cataSrc" (fun Γ ↦ [atPos 0 Γ]) [anyHyp, anyHyp] fun Γ Φ ψ ↦
          K.byHyp (Φ.length - 1) Γ Φ ψ) [] [] φ
      | dbgTrace "cataHeaded: not proved" fun _ ↦ none
    pure (⟨0, [], [], φ⟩, d))

/-- The development of the soundness at a structural recursion's source form. -/
def cataSrcDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  cataShapeDev P S T ++ [cataSrc P S T, cataHeaded P S T]

/-- The soundness at a structural recursion's source form, after that at its expanded form. -/
def cataSrcCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := caseNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (caseDev P S T).map (·.1) ++ (clausesDev P S T).map (·.1) ++
    (caseSoundDev P S T).map (·.1) ++ (cataDev P S T).map (·.1) ++
    (cataClausesDev P S T).map (·.1) ++ (cataChainDev P S T).map (·.1) ++
    (cataSoundDev P S T).map (·.1) ++ (cataCoreDev P S T).map (·.1)) "datatype-cata-src"
    (cataSrcDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
