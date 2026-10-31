/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeAssembly
public import GebTests.Prototypes.FreeTopos.DatatypeDatum
public meta import GebTests.Prototypes.FreeTopos.DatatypeDatum -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at decodings

The soundness of the datatype language's stage-1 compiler
({lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`) at a decoding, which the erasure writes as the
binding of the name {lit}`%e` to the decoded tree around the conditional on the datatype's
recognizer: the function applied to the tree where the recognizer accepts it, the default
otherwise. The typing reads the function and the default in the named context extended by the
binding, and requires that the reader read the recognizer's name as written
({lit}`Typing.readAsName`). The recognizers among the definitions decide membership
({lit}`Defs3.recsT`), and a member's quotation is related at its datatype ({lit}`relTDatum`).

## Main definitions

* {lit}`recognizerIn` — a datatype's name among names makes its recognizer's name the recognizer
  of one of them.
* {lit}`decodeBody` — the conditional the erasure writes converges to a value related at the
  result type.
* {lit}`decodeTyped` — the kernel types the elements of a decoding's resolution where it types
  the resolution.
* {lit}`decodeCase` — the soundness at a decoding.

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

/-- A datatype's name among names makes its recognizer's name the recognizer of one of them
({lit}`Typing.isRecognizer`): by induction on the names; at a construction, the head equal to the
name or not. Equal, the recognizer's name is equal to itself; unequal, the induction hypothesis at
the rest. -/
def recognizerIn (P : Prog) (S : Defs) : Step :=
  ("recognizerIn", fun ix E ↦ do
    -- the search among the names unfolded, by which the induction proceeds
    let K : Kit := ⟨{ P with folded := P.folded.filter (· != "Typing.hasName") }, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    -- under the quantifier: the name v0, the names v1
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (truth o (pc P "Typing.hasName" [v 0, v 1]))
      (truth o (pc P "Typing.isRecognizer" [v 1, pc P "Typing.recognizerName" [v 0]]))))
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let d₀ ← dAllI L (dImpI L (linkK K "recognizerIn: empty" lastFalse)) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the name, the rest, the head; hypotheses: the induction hypothesis, the
    -- quantifier's truth, the name's being among the names
    let cons : Deducer := dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let hd := at_ 0
      let n := at_ 2
      let rn (Γ : List Tree) : Term := pc P "Typing.recognizerName" [n Γ]
      let found := Φ₁.length - 1
      -- the head the name: the recognizer's name equal to itself
      let equalCase : Deducer := linkK K "recognizerIn: the head" <|
        K.cutThm "equalSound" (fun Γ ↦ [hd Γ]) <| K.allEΓ n <| K.impE (K.solve 3) <|
        K.cutThm "equalRefl" (fun Γ ↦ [rn Γ]) <|
        decideIn K (fun Γ ↦ apps equalT [rn Γ, rn Γ]) (anyFalse K) (K.solve 3)
      -- another: the induction hypothesis at the name, the head's recognizer's name equal to the
      -- name's or not, either proving the goal
      let rest : Deducer := linkK K "recognizerIn: the rest" fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (n Γ) (K.impE (K.byHyp found)
          (decideIn K (fun Γ ↦ apps equalT [rn Γ, pc P "Typing.recognizerName" [hd Γ]])
            (K.auto 3) (K.auto 3))) Γ Φ ψ
      decideIn K (fun Γ ↦ apps equalT [hd Γ, n Γ]) rest equalCase Γ₁ Φ₁ ψ₁)
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The equation of a test's label with the empty bitstring, as the case analysis of lists
({lit}`listCases`) states it, the theorem of index {lit}`jL` among the entries. -/
def nilEq (E : Array Internal.Entry) (jL : ℕ) (X : Term) : Option Term := do
  let some (Internal.Entry.language c) := E[jL]? | none
  RoseTree.para (fun l (cs : List (Term × Option Term)) ↦
    let t := RoseTree.node l (cs.map Prod.fst)
    match Internal.eqParts t with
    | some (a, _) => if a == X then some t else cs.findSome? (·.2)
    | none => cs.findSome? (·.2)) (Internal.instTerm [bitTy] [X] c.concl)

/-- The conjunction of formulas, the last alone at the end; truth for none. -/
def conjAll (o : ℕ) : List Term → Term
  | [] => Internal.Logic.tt o
  | ts => (ts.dropLast.foldr (Internal.Logic.conj o) (ts.getLast?.getD (Internal.Logic.tt o)))

/-- A name without an index among names ({lit}`Reader.indexOf`) is unequal to each: by induction on
the names; at a construction, the head equal to the name or not, then the rest's index present or
not. Equal, or the rest's index present, the construction's index is present, refuting the
hypothesis; otherwise the induction hypothesis at the rest. The index is unfolded one construction
at a time by its equations, the rest's kept folded. -/
def indexAbsent (P : Prog) (S : Defs) : Step :=
  ("indexAbsent", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    -- under the quantifier: the name v0, the names v1
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (notT o (isSomeT (pc P "Reader.indexOf" [v 0, v 1])))
      (S.allL (Term.lam treeTy (Term.eq (call D.lab [] [apps equalT [v 1, v 0]]) (nilT bitTy)))
        (v 1))))
    let d₀ ← dAllI L (dImpI L (linkK K "indexAbsent: empty" (K.solve 3))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the name, the rest, the head; hypotheses: the induction hypothesis, the
    -- quantifier's truth, the name's index absent
    let cons : Deducer := dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let hd := at_ 0
      let n := at_ 2
      let absent := Φ₁.length - 1
      -- the construction's index present, refuting its absence
      let present : Deducer := dImpE L absent (K.solve 3) fun Γ Φ ψ ↦
        K.hypFalse (Φ.length - 1) Γ Φ ψ
      -- the rest's index absent: the induction hypothesis at the name
      let rest : Deducer := linkK K "indexAbsent: the rest" fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (n Γ) (K.impE (dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)
          (K.auto 3)) Γ Φ ψ
      decideIn K (fun Γ ↦ apps equalT [n Γ, hd Γ])
        (decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf" [n Γ, at_ 1 Γ]])
          rest present)
        present Γ₁ Φ₁ ψ₁)
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A tree of the label of atoms is the atom of its children: the tree a node of its label and
children ({lit}`treeNode`), the label the atoms'. -/
def atomEta (P : Prog) (S : Defs) : Step :=
  ("atomEta", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let a : Internal.Thm := ⟨0, [treeTy], [Term.eq (call D.lab [] [v 0]) (numeral 1)],
      Term.eq (nodeT (Term.pair (numeral 1) (call D.children [] [v 0]))) (v 0)⟩
    let some d := K.treeNode (v 0) (fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 (linkK K "atomEta" (K.solve 3)) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "atomEta: not proved" fun _ ↦ none
    pure (a, d))

/-- A name that no reserved name equals ({lit}`Reader.reservedNames`) is unequal to each: the
equality's test with each reserved name false, the equations' conjunction, by
{name}`indexAbsent` at the reserved names. In the context of the name. -/
def reservedUnequal (P : Prog) (S : Defs) : Step :=
  ("reservedUnequal", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let names ← nfE K.G K.E (K.rules []) [] (pc P "Reader.reservedNames" [])
    let kws := (consCells names).map Prod.fst
    let test (kw : Term) : Term := apps equalT [v 0, kw]
    let eqs ← kws.mapM fun kw ↦ do
      nilEq E (ix "listCases") (← nfE K.G K.E (K.rules []) [treeTy] (call D.lab [] [test kw]))
    let φ := conjAll o eqs
    let hyp := notT o (truth o (pc P "Prelude.isSome" [pc P "Reader.indexOf"
      [v 0, pc P "Reader.reservedNames" []]]))
    -- the conjunction over the names unfolded and split, its equations rewriting the goal's
    let some d := (K.cutThm "indexAbsent" (fun _ ↦ [pc P "Reader.reservedNames" []]) <|
        K.allEΓ (fun _ ↦ v 0) <| K.impE K.anyHyp <| normLastK K <|
        (List.range eqs.length).foldr (fun _ k ↦ K.conjE k) (K.solve (eqs.length + 2)))
        [treeTy] [hyp] φ
      | dbgTrace "reservedUnequal: not proved" fun _ ↦ none
    pure (⟨0, [treeTy], [hyp], φ⟩, d))

/-- The statement that no keyword the reader reads names a source form's erasure with the numeral
abbreviations expanded ({name}`readerKeywords`): where the abbreviations cohere with a typing
environment, the form's expansion is a source form and present, and it has a type in a named
context. In the context of the form, the named context, the typing environment, the numeral
abbreviations and the expansion's declarations. -/
def srcHeadFreeThm (P : Prog) (T : Defs3) : Internal.Thm :=
  let x := pc P "Prelude.get" [pc P "Datatype.expandExpr" [v 4, v 0]]
  let isSomeT (t : Term) : Term := truth P.o (pc P "Prelude.isSome" [t])
  ⟨0, [treeTy, list treeTy, T.envTy, list treeTy, list treeTy],
    [T.numsT (v 2) (v 3),
      truth P.o (pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [v 4, v 0]), x]),
      isSomeT (pc P "Datatype.expandExpr" [v 4, v 0]),
      isSomeT (pc P "Typing.synIn" [v 2, v 1, x])],
    conjAll P.o (readerKeywords.map
      (unnamed P (pc P "Reader.expandNums" [v 3, pc P "Datatype.eraseExpr" [x]])))⟩

/-- No keyword the reader reads names a source form's erasure with the numeral abbreviations
expanded ({name}`srcHeadFreeThm`), the form's label decided. An atom is its own expansion and
erasure: its name decided against each keyword, a keyword's refuting the typing; its characters
fixed, else the test of source forms is refuted; abbreviated, the abbreviation's numeral named by
no keyword ({name}`numeralUnnamed`). A list's erasure and that erasure with the abbreviations
expanded are lists ({name}`eraseList`, {name}`numsListThm`), which no keyword names
({name}`namedListThm`). A form of any other label expands to no source form. -/
def srcHeadFree (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("srcHeadFree", fun ix E ↦ do
    let K := appKit P S ix E
    let W : KwKit := { kwKit P S T ix E 0 [] with K := K }
    let L := K.L
    let a := srcHeadFreeThm P T
    let childrenT ← primT Kernel.Prim.children
    let decls := atPos 0
    let nums := atPos 1
    let fnOf (Γ : List Tree) : Term :=
      Term.lam treeTy (pc P "Reader.expandNums" [Term.rename (nums Γ) (· + 1), v 0])
    let unfold := ((List.range nFolds).map T.argIdx).map Internal.NormRule.delta
    let solveU : Deducer := fun Γ Φ ψ ↦
      dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold) .full) (K.solve (readerKeywords.length + 2))
        Γ Φ ψ
    let refute (msg : String) : Deducer := linkK K s!"srcHeadFree: {msg}" fun Γ Φ ψ ↦
      (anyFalse K Γ Φ ψ).orElse fun _ ↦ (W.hypFalseU 3 Γ Φ ψ).orElse fun _ ↦
        (W.hypFalseU 1 Γ Φ ψ).orElse fun _ ↦ W.hypFalseU 2 Γ Φ ψ
    -- an atom, of the characters of position csPos: its name against each keyword's, its
    -- characters fixed, its abbreviation decided
    let atom (csPos : ℕ) : Deducer :=
      let cs (Γ : List Tree) : Term := atPos csPos Γ
      let nm (Γ : List Tree) : Term := nameOfChars P (cs Γ)
      -- abbreviated: the abbreviation the atom of a numeral, whose name no keyword's is
      let abbreviated : Deducer := linkK K "srcHeadFree: the abbreviation" <|
        dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) 0 fun Γ Φ ψ ↦
        dAllE L K.G K.E (Φ.length - 1) (nm Γ) (K.conjE fun Γ Φ ψ ↦
          let (n₁, n₂) := (Φ.length - 2, Φ.length - 1)
          dImpE L n₂ (K.solve 3) (fun Γ Φ ψ ↦
            dImpE L n₁ (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) (K.exE <| K.conjE
              fun Γ Φ ψ ↦
              let iNum := Φ.length - 1
              let dsPos := Γ.length - 1
              (readerKeywords.foldr (fun kw k ↦ W.cutApply s!"numeralUnnamed/{kw}"
                  (fun Γ ↦ [atPos dsPos Γ]) [K.byHyp iNum] k) solveU) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
          Γ Φ ψ
      readerKeywords.foldr (fun kw k ↦
        decideBits K (fun Γ ↦ call D.equal [] [nm Γ, pc P kw []]) k
          (linkK K s!"srcHeadFree: the keyword {kw}" <|
          K.cutThm "equalSound" (fun Γ ↦ [nm Γ]) <| K.allEΓ (fun _ ↦ pc P kw []) <|
          K.impE (K.solve 3) fun Γ Φ ψ ↦
          K.image (Φ.length - 1) (fun t ↦ apps childrenT [t])
            (refute s!"the keyword {kw}") Γ Φ ψ))
        (decideIn K (fun Γ ↦ pc P "charsFixed" [fnOf Γ, cs Γ]) (refute "characters not fixed") <|
          K.cutThm "charsFixedEq" (fun Γ ↦ [cs Γ, nums Γ]) <| K.impE (K.solve 3) <|
          decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [nm Γ, nums Γ]])
            solveU abbreviated)
    -- a list, of the elements of position hcsPos: its erasure a list, and that erasure with the
    -- abbreviations expanded, which no keyword names
    let listB (hcsPos : ℕ) : Deducer :=
      let hcs (Γ : List Tree) : Term := atPos hcsPos Γ
      let g (Γ : List Tree) : Term := pc P "Datatype.eraseExpr" [pc P "Prelude.get"
        [pc P "Datatype.expandExpr" [decls Γ, nodeT (Term.pair (numeral 2) (hcs Γ))]]]
      let view (Γ : List Tree) : Term := pc P "Reader.expandNums" [nums Γ, g Γ]
      linkK K "srcHeadFree: a list" <|
      W.cutApply "eraseList" (fun Γ ↦ [hcs Γ, decls Γ])
        [fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ K.byHyp 2 Γ Φ ψ] <| fun Γ Φ ψ ↦
      -- each premise the equation cut before it, which normalizes by itself to an equation of a
      -- term with itself
      let byLast (i : ℕ) : Deducer := fun Γ Φ ψ ↦
        (K.solve 3 Γ Φ ψ).orElse fun _ ↦ K.byHyp i Γ Φ ψ
      linkK K "srcHeadFree: the erasure a list"
        (W.cutApply "numsList" (fun Γ ↦ [g Γ, nums Γ]) [byLast (Φ.length - 1)] (fun Γ Φ ψ ↦
          let isList := Φ.length - 1
          linkK K "srcHeadFree: its expansion a list" (readerKeywords.foldr (fun kw k ↦
            W.cutApply (namedListName kw) (fun Γ ↦ [view Γ]) [byLast isList] (normLastK K k))
            (linkK K "srcHeadFree: the keywords" (K.solve (readerKeywords.length + 2)))) Γ Φ ψ))
          Γ Φ ψ
    let some d := K.treeNode (v 0) (fun Γ Φ ψ ↦
        let (lPos, csPos) := (Γ.length - 2, Γ.length - 1)
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          match bs.map Oitavem.rank with
          | some 1 => K.norm (atom csPos)
          | some 2 => K.norm (listB csPos)
          | _ => refute "another label") 2 [] (atPos lPos Γ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "srcHeadFree: not proved" fun _ ↦ none
    pure (a, d))

/-- The name of a form's characters, as the typing compares names. -/
def nameOfForm (P : Prog) (f : Term) : Term := nameOfChars P (call D.children [] [f])

/-- The recognizer's name of the datatype a form names. -/
def recOfForm (P : Prog) (f : Term) : Term :=
  pc P "Typing.recognizerName" [nameOfForm P f]

/-- What a datatype's naming by a form gives ({lit}`Typing.namesData`), in the context of the
form, the type and the typing environment: the form an atom, whose name the environment declares,
and the recognizer's name of that name, which the reader reads as written
({lit}`Typing.readAsName`): reserved by no reserved name, not the implementation's, no numeral, and
not abbreviated. -/
def namesDataPartsThm (P : Prog) (T : Defs3) : Internal.Thm :=
  let o := P.o
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let rn := recOfForm P (v 0)
  let rnCs := call D.children [] [rn]
  ⟨0, [treeTy, treeTy, T.envTy], [truth o (pc P "Typing.namesData" [v 2, v 1, v 0])],
    conjAll o [Term.eq (call D.lab [] [v 0]) (numeral 1),
      truth o (pc P "Typing.hasName" [nameOfForm P (v 0), pc P "Typing.envNoms" [v 2]]),
      notT o (isSomeT (pc P "Reader.indexOf" [rn, pc P "Reader.reservedNames" []])),
      notT o (truth o (pc P "implName" [rn])),
      notT o (isSomeT (pc P "Reader.numeral" [rnCs])),
      notT o (truth o (pc P "Typing.hasName" [rn, pc P "Typing.envNums" [v 2]]))]⟩

/-- What a datatype's naming by a form gives ({name}`namesDataPartsThm`): the naming unfolded, the
type a node, the tests its normal form is blocked on decided, false refuting it; the name the
naming compares the form's, by the equality's soundness, its characters the form's; each part
then by normalization, a hypothesis, or its negation's test refuted. -/
def namesDataParts (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("namesDataParts", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, vocab3.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let L := K.L
    let a := namesDataPartsThm P T
    let childrenT ← primT Kernel.Prim.children
    let namesD := Internal.NormRule.delta (P.idx "Typing.namesData")
    -- a part: conjunctions split, negations by refuting the negated test, others by
    -- normalization or a hypothesis
    let part : Deducer := (8 : ℕ).rec (fun _ _ _ ↦ none) fun _ rec Γ Φ ψ ↦
      match defnParts ψ with
      | some (i, _, _) =>
        if i = P.o + 1 then dConjI L rec rec Γ Φ ψ
        else (dImpI L (fun Γ Φ ψ ↦ anyFalse K Γ Φ ψ) Γ Φ ψ).orElse fun _ ↦
          (K.solve 3 Γ Φ ψ).orElse fun _ ↦ linkK K "namesDataParts: a part" K.anyHyp Γ Φ ψ
      | none => (K.solve 3 Γ Φ ψ).orElse fun _ ↦
          linkK K "namesDataParts: a part" K.anyHyp Γ Φ ψ
    -- the names' equality among the hypotheses, by its soundness, and the names' children
    let named : Deducer := fun Γ Φ ψ ↦ do
      let some (x, y) := (List.range Φ.length).reverse.findSome? fun h ↦ do
          let (n, _) ← evalRw K.G K.E (K.rulesEx Φ h) .full Γ Φ (← Φ[h]?)
          equalArgs n
        | traceK K "namesDataParts: no equality" Γ Φ ψ
      -- the equations before the names' rewritten by the others, the declared name the form's;
      -- and by the others but the names' own, so that the declared name's children become the
      -- form's by their image
      let byChildren (k : Deducer) : Deducer := fun Γ Φ ψ ↦
        let nameEq := Φ.length - 2
        let sides := ((Φ[nameEq]?).bind Internal.eqParts).map (fun (a, b) ↦ [a, b]) |>.getD []
        let mentions (t : Term) : Bool := RoseTree.para (fun l (cs : List (Term × Bool)) ↦
          sides.contains (RoseTree.node l (cs.map Prod.fst)) || cs.any (·.2)) t
        let hs := (List.range nameEq).filter fun h ↦
          (Φ[h]?.bind Internal.eqParts).isSome && (Φ[h]?.map mentions).getD false
        hs.foldr (fun h k Γ Φ ψ ↦
          let rs := (K.rules Φ).filter fun r ↦ match r with
            | .hyp j => j ≠ h ∧ j ≠ nameEq
            | _ => true
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h
            (dRwHyp (evalRw K.G K.E rs .full) h k) Γ Φ ψ) k Γ Φ ψ
      let attempt (x y : Term) : Deducer :=
        K.cutThm "equalSound" (fun _ ↦ [x]) <| K.allEΓ (fun _ ↦ y) <|
        K.impE (K.solve 3) fun Γ Φ ψ ↦
        K.image (Φ.length - 1) (fun t ↦ apps childrenT [t]) (byChildren (K.norm part)) Γ Φ ψ
      (attempt x y Γ Φ ψ).orElse fun _ ↦ attempt y x Γ Φ ψ
    let some d := (dRwHyp (evalRw K.G K.E (K.rules [] ++ [namesD]) .full) 0 <|
        K.treeNode (v 1) (K.splitHyp 1 (fun Γ Φ ψ ↦ (anyFalse K Γ Φ ψ).orElse fun _ ↦
          named Γ Φ ψ) 64)) a.ctx a.hyps a.concl
      | dbgTrace "namesDataParts: not proved" fun _ ↦ none
    pure (a, d))

/-- The kernel's variable of index zero. -/
def var0T : Term :=
  nodeT (Term.pair (numeral Kernel.Label.var) (consT treeTy (leafT bnilT) (nilT treeTy)))

/-- The kernel's conditional of a condition over two branches. -/
def condK (c a b : Term) : Term :=
  nodeT (Term.pair (numeral Kernel.Label.cond)
    (consT treeTy c (consT treeTy a (consT treeTy b (nilT treeTy)))))

/-- The arrow type of two types. -/
def arrowTy (A B : Term) : Term := nodeT (Term.pair (numeral Kernel.Label.tyArrow)
  (consT treeTy A (consT treeTy B (nilT treeTy))))

/-- The statement of the convergence of the decoding's body, the conditional the erasure writes in
the scope of the decoded tree: for each value related at the tree type, where in the environment
extended by it the recognizer's term converges to a function deciding membership in the datatype
of the name {lit}`d`, the function's term to a value related at the arrow type from the datatype
{lit}`D` to the result type and the default's term to a value related at the result type, and a
member's quotation is related at {lit}`D`, the conditional converges to a value related at the
result type. In the context of the environment, the function's, the default's and the
recognizer's terms, the name, the datatype, the result type and the relation's context. -/
def decodeBodyThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  let o := P.o
  let imp := Internal.Logic.imp o
  let all := Internal.Logic.all o
  let ex := Internal.Logic.ex o
  let conj := Internal.Logic.conj o
  let sh (k : ℕ) (t : Term) : Term := Term.rename t (· + k)
  -- the convergence of a term's evaluation in an environment to a value the predicate holds of
  let convIn (R env t pred : Term) : Term :=
    S.conv (Term.lam nat (S.evN (Term.fst (sh 1 R)) (v 0) (sh 1 env) (sh 1 t))) pred
  -- the context, the innermost first, at a depth of binders
  let R (k : ℕ) : Term := v (7 + k)
  let cty (k : ℕ) : Term := v (6 + k)
  let dty (k : ℕ) : Term := v (5 + k)
  let nm (k : ℕ) : Term := v (4 + k)
  let A (k : ℕ) : Term := v (3 + k)
  let C (k : ℕ) : Term := v (2 + k)
  let F (k : ℕ) : Term := v (1 + k)
  let env (k : ℕ) : Term := v k
  let member (k : ℕ) (t : Term) : Term := truth o (pc P "Typing.memberOf"
    [Term.snd (R k), nodeT (Term.pair (numeral 1) (call D.children [] [nm k])), t])
  -- for each value x related at the tree type, x the innermost variable
  let atX (body : Term) : Term := all treeTy (Term.lam treeTy
    (imp (Term.app (T.relT (R 1) (leafT bnilT)) (v 0)) body))
  -- under x, the value g, the tree t, the value w: w the quotation of a tree true exactly when t
  -- is a member
  let agrees : Term := ex treeTy (Term.lam treeTy (conj
    (Term.eq (v 1) (pc P "Eval.valQuote" [v 0]))
    (conj (imp (truth o (v 0)) (member 5 (v 2))) (imp (member 5 (v 2)) (truth o (v 0))))))
  let decides : Term := Term.lam treeTy (all treeTy (Term.lam treeTy
    (S.conv (Term.lam nat (apps (Term.snd (S.levelN (Term.fst (R 4)) (v 0)))
      [v 2, pc P "Eval.valQuote" [v 1]])) (Term.lam treeTy agrees))))
  let xEnv : Term := consT treeTy (v 0) (env 1)
  ⟨0, [list treeTy, treeTy, treeTy, treeTy, treeTy, treeTy, treeTy, Defs3.ctxTy],
    [atX (convIn (R 1) xEnv (F 1) (T.relT (R 1) (arrowTy (dty 1) (cty 1)))),
      atX (convIn (R 1) xEnv (C 1) (T.relT (R 1) (cty 1))),
      atX (convIn (R 1) xEnv (A 1) decides),
      all treeTy (Term.lam treeTy (imp (member 1 (v 0))
        (Term.app (T.relT (R 1) (dty 1)) (pc P "Eval.valQuote" [v 0]))))],
    atX (convIn (R 1) xEnv (condK (appT (A 1) var0T) (appT (F 1) var0T) (C 1))
      (T.relT (R 1) (cty 1)))⟩

/-- The decoding's body converges ({name}`decodeBodyThm`): the value a tree's quotation
({lit}`relTTree`); the recognizer's convergence and its application's to the quotation, a
quotation of a tree whose label decides the branch. Empty, the default's convergence; not, the
tree a member, its quotation related at the datatype, and the function's convergence and its
application's at the value ({lit}`relTArrow`). The thresholds shifted to their sum
({name}`Kit.sumShift`), at whose successor the conditional evaluates, its condition and branches
at that level and the applications a level below. -/
def decodeBody (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("decodeBody", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, ["relTTree", "relTArrow"]⟩
    let L := K.L
    let a := decodeBodyThm P S T
    -- the stabilities, of the thresholds and values of the positions given, instantiated at the
    -- successor of the level below or at it, then the value related by the hypothesis rel
    let finish (ns : List ℕ) (here : List Bool) (w rel : ℕ) (hs : List ℕ) : Deducer :=
      fun Γ Φ ψ ↦
      let sum := (K.sumOf (ns.map atPos)).getD fun _ ↦ zeroN
      K.conv (fun Γ ↦ succN (sum Γ)) (atPos w)
        ((hs.zip here).foldr (fun ((h, up) : ℕ × Bool) k ↦
            K.instN h (fun _ ↦ if up then succN (v 0) else v 0) k)
          (linkK K "decodeBody stable" K.byNorm))
        (linkK K "decodeBody related" (K.byHyp rel)) Γ Φ ψ
    -- context: the value x, of position px; the tree t its quotation's, of position px + 1
    let px := a.ctx.length
    let (pt, relX) := (px + 1, a.hyps.length + 1)
    -- the default's convergence at the value; the thresholds the recognizer's and its
    -- application's, of positions pa and pb, and their stabilities
    let default (pa pb sa sb : ℕ) : Deducer := linkK K "decodeBody: the default" fun Γ Φ ψ ↦
      dAllE L K.G K.E 1 (atPos px Γ) (K.impE (K.byHyp relX) (K.convE fun Γ₅ Φ₅ ψ₅ ↦
        let pc := Γ₅.length - 2
        K.sumShift ([pa, pb, pc].map atPos) [sa, sb, Φ₅.length - 2]
          (finish [pa, pb, pc] [true, false, true] (pc + 1) (Φ₅.length - 1)) Γ₅ Φ₅ ψ₅)) Γ Φ ψ
    -- the tree a member, its quotation related at the datatype; the function's convergence at
    -- the value and its value's application to it ({lit}`relTArrow`)
    let function (pa pb sa sb toMember : ℕ) : Deducer :=
      linkK K "decodeBody: the function" fun Γ Φ ψ ↦
      dImpE L toMember (K.solve 3) (fun Γ Φ ψ ↦
        dAllE L K.G K.E 3 (atPos pt Γ) (K.impE (K.byHyp (Φ.length - 1)) fun Γ Φ ψ ↦
          let relD := Φ.length - 1
          dAllE L K.G K.E 0 (atPos px Γ) (K.impE (K.byHyp relX) (K.convE fun Γ₅ Φ₅ ψ₅ ↦
            let (pf, sf) := (Γ₅.length - 2, Φ₅.length - 2)
            K.normLast (K.allEΓ (atPos px) (K.impE (K.byHyp relD) (K.convE fun Γ₆ Φ₆ ψ₆ ↦
              let pp := Γ₆.length - 2
              K.sumShift ([pa, pb, pf, pp].map atPos) [sa, sb, sf, Φ₆.length - 2]
                (finish [pa, pb, pf, pp] [true, false, true, false] (pp + 1) (Φ₆.length - 1))
                Γ₆ Φ₆ ψ₆))) Γ₅ Φ₅ ψ₅)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    -- the application's value the quotation of a tree u, of position pb + 2, whose label decides
    -- the branch
    let branches (pa pb sa sb : ℕ) : Deducer :=
      K.normLast <| K.exE <| K.conjE <| K.conjE fun Γ Φ ψ ↦
        let toMember := Φ.length - 2
        match evalRw K.G K.E (K.rules Φ) .full Γ Φ (call D.lab [] [atPos (pb + 2) Γ]) with
        | some (Y, _) => K.listCase bitTy Y (default pa pb sa sb)
            (function pa pb sa sb toMember) Γ Φ ψ
        | none => traceK K "decodeBody: no label" Γ Φ ψ
    -- the recognizer's convergence at the value, its value's application's to the tree's
    -- quotation
    let recognizer : Deducer := fun Γ Φ ψ ↦
      dAllE L K.G K.E 2 (atPos px Γ) (K.impE (K.byHyp relX) <| K.convE fun Γ₂ Φ₂ ψ₂ ↦
        let (pa, sa) := (Γ₂.length - 2, Φ₂.length - 2)
        K.normLast (K.allEΓ (atPos pt) (K.convE fun Γ₃ Φ₃ ψ₃ ↦
          branches pa (Γ₃.length - 2) sa (Φ₃.length - 2) Γ₃ Φ₃ ψ₃)) Γ₂ Φ₂ ψ₂) Γ Φ ψ
    -- the value a tree's quotation, then the recognizer's convergence
    let d? := dAllI L <| dImpI L <| K.normLast <| K.exE recognizer
    let some d := d? a.ctx a.hyps a.concl | dbgTrace "decodeBody: not proved" fun _ ↦ none
    pure (a, d))

/-- The typing's tests at a decoding, which the soundness at a decoding decides whole. -/
def decodeTests : List String := ["Typing.namesData"]

/-- The expansion of the numeral abbreviations maps the concatenation of two lists of trees to the
concatenation of their maps, as it maps the characters of a recognizer's name: by induction on the
first list, at a construction the induction hypothesis at the second and the abbreviations. -/
def mapAppend (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("mapAppend", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let f ← (foldSpecs P T.envTy)[3]?
    let (_, d, _, _, _, _) ← foldDefn P f (T.argIdx 3)
    let Ls := list treeTy
    let mapAt (xs nums : Term) : Term := Term.subst (mapFold T 3 d.type d.params.tail) fun i ↦
      if i = 0 then xs else if i = 1 then nums else v i
    let append (xs ys : Term) : Term :=
      foldrT treeTy Ls (Term.lam treeTy (Term.lam Ls (consT treeTy (v 1) (v 0)))) ys xs
    -- under the quantifiers: the abbreviations v0, the second list v1, the first v2
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o Ls (Term.lam Ls
      (Term.eq (mapAt (append (v 2) (v 1)) (v 0))
        (append (mapAt (v 2) (v 0)) (mapAt (v 1) (v 0)))))))
    let d₀ ← dAllI L (dAllI L K.byNorm) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a construction: the induction hypothesis, the first hypothesis, at the second list and the
    -- abbreviations
    let cons : Deducer := dAllI L <| dAllI L <| dAllE L K.G K.E 0 (v 1) fun Γ Φ ψ ↦
      dAllE L K.G K.E (Φ.length - 1) (v 0) (normLastK K K.byNorm) Γ Φ ψ
    let d₁ ← cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The equation of {name}`mapAppend` at the first list v2, the second v1 and the abbreviations v0,
a rule for the normal forms. -/
def mapAppendEq (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("mapAppendEq", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let f ← (foldSpecs P T.envTy)[3]?
    let (_, d, _, _, _, _) ← foldDefn P f (T.argIdx 3)
    let Ls := list treeTy
    let mapAt (xs nums : Term) : Term := Term.subst (mapFold T 3 d.type d.params.tail) fun i ↦
      if i = 0 then xs else if i = 1 then nums else v i
    let append (xs ys : Term) : Term :=
      foldrT treeTy Ls (Term.lam treeTy (Term.lam Ls (consT treeTy (v 1) (v 0)))) ys xs
    let a : Internal.Thm := ⟨0, [Ls, Ls, Ls], [], Term.eq (mapAt (append (v 2) (v 1)) (v 0))
      (append (mapAt (v 2) (v 0)) (mapAt (v 1) (v 0)))⟩
    let some d := (K.cutThm "mapAppend" (fun _ ↦ [v 2]) <| K.allEΓ (fun _ ↦ v 1) <|
        K.allEΓ (fun _ ↦ v 0) K.byNorm) a.ctx a.hyps a.concl
      | dbgTrace "mapAppendEq: not proved" fun _ ↦ none
    pure (a, d))

/-- The stage functions' equations at the keywords of a decoding's expansion, a let over a test,
in the normal form of the rules after the development at decodings ({name}`kwEqs`), the tests of
{name}`decodeTests` folded. -/
def expansionEqs (P : Prog) (T : Defs3) : List Step :=
  [("Reader.kwLet", 4), ("Reader.kwIf", 3)].flatMap fun (kw, n) ↦
    kwEqs { P with folded := P.folded ++ decodeTests } T kw n (tag := "/decode")

/-- The reduction of the subterms of a term that a test selects, innermost first: each selected
subterm, after its own selected subterms, reduced by {lit}`ev`, and the term rebuilt about the
reduced subterms by congruence, so that a selected subterm reaches {lit}`ev` with its selected
subterms in normal form, not to be reduced at each of their copies. The children in contexts of
their own, those of abstractions and the starts and steps of folds, are left in place, their
reductions, delayed, not computed. -/
def reduceInnermost (sel : Term → Bool)
    (ev : Term → Option (Term × Internal.Deriv × Bool)) (t : Term) :
    Option (Term × Internal.Deriv × Bool) :=
  RoseTree.para (fun l (cs : List (Term × (Unit → Option (Term × Internal.Deriv × Bool)))) _ ↦
    do
      let rs ← cs.zipIdx.mapM fun ((u, r), i) ↦
        if Internal.keepsWeak l i then some (u, Internal.dRefl) else r ()
      let t₁ := RoseTree.node l (rs.map Prod.fst)
      let d₁ := Internal.dCong (rs.map Prod.snd)
      if sel t₁ then
        let (t₂, d₂) ← ev t₁
        pure (t₂, Internal.dTrans d₁ d₂)
      else pure (t₁, d₁)) t ()

/-- The distinct subterms of a term that a test selects, outside the children in contexts of their
own, those of abstractions and the starts and steps of folds, each after those within it. -/
def collectOutside (sel : Term → Bool) : Term → List Term :=
  RoseTree.para fun l (cs : List (Term × List Term)) ↦
    let below := cs.zipIdx.foldl (fun acc ((_, ts), i) ↦ if Internal.keepsWeak l i then acc
      else ts.foldl (fun a x ↦ if a.contains x then a else a ++ [x]) acc) []
    let t := RoseTree.node l (cs.map Prod.fst)
    if sel t && !below.contains t then below ++ [t] else below

/-- The subterms of a term in a context, each with its context and whether it is a node whose
children are among them. -/
abbrev KOrder : Type := Term → List (Term × Term × Bool)

/-- The subterms of a resolved term whose types the kernel's typing tests, each with its context
and whether it is a node whose children are among them, its children in the order the typing
tests them, after the node where {lit}`pre` holds, before it otherwise: those of an abstraction's
body in the context extended by its annotation, those of the children of an application, a pair,
a projection, a conditional or a construction of a list in the node's context; a term not such a
node is tested as a whole. A label is recognized by its numeral's normal form, {lit}`lbl`. -/
def kernelOrder (lbl : ℕ → Term) (pre : Bool) (t ctx : Term) : List (Term × Term × Bool) :=
  (RoseTree.para (fun l (cs : List (Term × (KOrder × List (Term × KOrder) ×
      Option ((Term × KOrder) × List (Term × KOrder))))) ↦
    let t := RoseTree.node l (cs.map Prod.fst)
    -- the elements of a list, with their orders
    let elems : List (Term × KOrder) := match l, cs with
      | .arr 1 _, [(_, (_, _, some (h, tl)))] => h :: tl
      | _, _ => []
    -- a pair's first component, and its second's elements
    let parts : Option ((Term × KOrder) × List (Term × KOrder)) := match l, cs with
      | .pair, [(a, (oa, _, _)), (_, (_, es, _))] => some ((a, oa), es)
      | _, _ => none
    let order : KOrder := fun ctx ↦
      let kids : Option (List (Term × Term × Bool)) := match l, cs with
        | .arr 2 _, [(_, (_, _, some ((lb, _), kids)))] =>
          if lb == lbl Kernel.Label.lam then match kids with
            | [(A, _), (_, ob)] => some (ob (consT treeTy A ctx))
            | _ => none
          else if [Kernel.Label.app, Kernel.Label.pair, Kernel.Label.fst, Kernel.Label.snd,
              Kernel.Label.cond, Kernel.Label.cons].any (lb == lbl ·) then
            some (kids.flatMap (·.2 ctx))
          else none
        | _, _ => none
      let here := (ctx, t, kids.isSome)
      if pre then here :: kids.getD [] else kids.getD [] ++ [here]
    (order, elems, parts)) t).1 ctx

/-- Whether a term is an application of the kernel's typing to its three arguments. -/
def isTypeIn (P : Prog) (t : Term) : Bool := match t.label, t.children with
  | .app, [f, _] => match f.label, f.children with
    | .app, [g, _] => match g.label, g.children with
      | .app, [e, _] => match e.label with
        | .defn j _ => j == P.idx "Check.typeIn"
        | _ => false
      | _, _ => false
    | _, _ => false
  | _, _ => false

/-- The arguments of an application of the kernel's typing: the globals' types, the context and
the term. -/
def typeInArgs (t : Term) : Option (Term × Term × Term) := match t.children with
  | [f, R] => match f.children with
    | [g, ctx] => match g.children with
      | [_, G] => some (G, ctx, R)
      | _ => none
    | _ => none
  | _ => none

/-- A subterm's type in the kernel present, the goal, where the hypothesis {lit}`h` states a
term's type present, both with the typing folded: the term's nodes generalized, the innermost
first, each equal to the node of its children's variables; then the type of each node enclosing
the subterm, of each subterm the typing tests before it, and of the subterm decided present in the
order the typing tests them ({name}`kernelOrder`), absent refuting the hypothesis with the
equations of the nodes enclosing it left out, so that the typing is evaluated along that path
alone; then the goal by normalization. -/
def kernelTyped (K : Kit) (h : ℕ) : Deducer := fun Γ Φ ψ ↦
  let jT := K.ix "typeInRr"
  let folded (Φ : List Term) : List Internal.NormRule := (K.rulesEx Φ h).filter fun r ↦
    match r with
    | .thm j _ => j != jT
    | _ => true
  dRwHyp (evalRw K.G K.E (folded Φ) .full) h (dRwBy (evalRw K.G K.E (folded Φ) .full)
    fun Γ₀ Φ₀ ψ₀ ↦ do
    let h₀ := Φ₀.length - 1
    let some (G, ctx, R) := (match collectOutside (isTypeIn K.P) (Φ₀.getD h₀ Term.star) with
        | [ty] => typeInArgs ty
        | _ => none)
      | dbgTrace "kernelTyped: no typing in the hypothesis" fun _ ↦ none
    let some (_, c, s) := (match collectOutside (isTypeIn K.P) ψ₀ with
        | [ty] => typeInArgs ty
        | _ => none)
      | dbgTrace "kernelTyped: no typing in the goal" fun _ ↦ none
    let lbl (n : ℕ) : Term :=
      ((evalRw K.G K.E (K.rules []) .full Γ₀ [] (numeral n)).map Prod.fst).getD Term.star
    let sh (Γ : List Tree) (t : Term) : Term := Term.rename t (· + (Γ.length - Γ₀.length))
    -- whether a term occurs in another
    let within (u : Term) : Term → Bool :=
      RoseTree.para fun l (cs : List (Term × Bool)) ↦
        RoseTree.node l (cs.map Prod.fst) == u || cs.any (·.2)
    let nodes := (((kernelOrder lbl false R ctx).dropLast).filter (·.2.2)).map (·.2.1)
    let pre := (kernelOrder lbl true R ctx).drop 1
    let enclosing (u : Term) : List Term := nodes.filter fun N ↦ N != u && within u N
    let some i := pre.findIdx? fun (c', u, _) ↦ u == s && c' == c
      | dbgTrace s!"kernelTyped: {showT s} not tested" fun _ ↦ none
    let steps := (pre.take (i + 1)).filter fun (_, u, _) ↦ (enclosing u).all (within s ·)
    -- the types decided, each node's equation and variable of the positions given, a node's
    -- type that of its variable
    let decide (eqs : List (Term × ℕ × ℕ)) : Deducer :=
      steps.foldr (fun (c, u, _) k ↦
        let out := (enclosing u).filterMap fun N ↦ (eqs.find? (·.1 == N)).map (·.2.1)
        let uAt (Γ : List Tree) : Term := match eqs.find? (·.1 == u) with
          | some (_, _, p) => atPos p Γ
          | none => sh Γ u
        decideOpt K (fun Γ ↦ pc K.P "Check.typeIn" [sh Γ G, sh Γ c, uAt Γ])
          (fun Γ Φ ψ ↦
            -- the hypothesis's term rewritten by the equations of the nodes not enclosing the
            -- subterm alone, since the fold's equation at a node applies before its children
            -- are reduced, and then by the rules but those equations
            let folds := eqs.filterMap fun (_, e, _) ↦
              if out.contains e then none else some (Internal.NormRule.hyp e)
            let refute : Deducer := fun Γ Φ ψ ↦
              let h₁ := Φ.length - 1
              let rs := (K.rulesEx Φ h₁).filter fun r ↦ match r with
                | .hyp j => !out.contains j && j != h₀
                | _ => true
              dRwHyp (evalRw K.G K.E rs .full) h₁ (dFalse K.L dHyp) Γ Φ ψ
            dRwHyp (evalRw K.G K.E folds .full) h₀ refute Γ Φ ψ) k (minimal := true))
        (linkK K "kernelTyped: not solved" (K.solve 3))
    nodes.foldr (fun N k eqs ↦ generalizeK K (fun Γ ↦ sh Γ N) fun Γ Φ ψ ↦
      k (eqs ++ [(N, Φ.length - 1, Γ.length - 1)]) Γ Φ ψ) decide [] Γ₀ Φ₀ ψ₀) Γ Φ ψ

/-- The statement of the kernel's typing of the decoding's resolution at its elements: where the
kernel types the application of the abstraction over a tree of the conditional on a term's
application to the variable, between the function's application to it and the default, to the
tree, it types the function and the default in the context extended by the tree type and the tree
in the context. In the context of the tree, the default, the function, the conditional's term, the
kernel's context and the globals' types. -/
def decodeTypedThm (P : Prog) : Internal.Thm :=
  let o := P.o
  let typed (ctx t : Term) : Term :=
    truth o (pc P "Prelude.isSome" [pc P "Check.typeIn" [v 5, ctx, t]])
  let treeK := nodeT (Term.pair (numeral Kernel.Label.tyTree) (nilT treeTy))
  let inner := consT treeTy treeK (v 4)
  let R := appT (lamT treeK (condK (appT (v 3) var0T) (appT (v 2) var0T) (v 1))) (v 0)
  ⟨0, [treeTy, treeTy, treeTy, treeTy, list treeTy, list treeTy], [typed (v 4) R],
    conjAll o [typed inner (v 2), typed inner (v 1), typed (v 4) (v 0)]⟩

/-- The kernel's typing of the decoding's resolution at its elements ({name}`decodeTypedThm`):
each conjunct by {name}`kernelTyped`. -/
def decodeTyped (P : Prog) (S : Defs) : Step :=
  ("decodeTyped", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let a := decodeTypedThm P
    let part := kernelTyped K 0
    let some d := dConjI K.L part (dConjI K.L part part) a.ctx a.hyps a.concl
      | dbgTrace "decodeTyped: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at a decoding, at source forms: the keywords the erasure writes not
abbreviated; the elements' expansions present and source forms; the typing's types of the
elements present, each absent refuting the typing, and the tests of the typing's rule decided,
false refuting it: the datatype the form names ({lit}`Typing.namesData`), the decoded tree's type
the tree type, the function's type an arrow from the datatype to the default's. The naming's parts
({name}`namesDataParts`) make the type's form an atom and the recognizer's name one the reader
reads as written: no reserved name ({name}`reservedUnequal`), not the decoded tree's, abbreviated,
nor a numeral, nor in the scope of a context's name, which would make it the implementation's or
not the environment's recognizer ({name}`recognizerIn`). The resolutions of the function, the
default and the tree present, each absent refuting the statement's hypothesis of the resolution,
with the kernel's types of the elements ({name}`decodeTyped`); the value the application of the
abstraction of the conditional to the tree's term, related at the result type by
{name}`decodeBody`. -/
def decodeCase (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("decodeCase", fun ix E ↦ do
    let kw := "Typing.kwDecode"
    let ihs := [false, true, true, true]
    let W₀ := kwKit P S T ix E 4 ihs kw
    let W : KwKit := { W₀ with K := { W₀.K with
      P := { W₀.K.P with folded := W₀.K.P.folded ++ decodeTests },
      more := W₀.K.more ++ ["mapAppendEq"] } }
    let K := W.K
    let L := K.L
    let a := kwThm P S T kw 4 ihs
    let x := pc P "Prelude.get" [pc P "Datatype.expandExpr" [v 7, v nQ]]
    let typed (t : Term) : Term := Term.fst (Term.app (Term.snd (T.foldAt 1 [v 6] t)) Term.star)
    let tyForm := pc P "Datatype.expandAliases" [v 7, x]
    let readTy := pc P "Typing.readTy" [v 6, typed tyForm]
    let tyT := (datatypeTerms P (v nQ)).1
    -- the named context extended by the decoded tree's entry, at the tree type
    let entry : Term := pc P "Typing.abbr"
      [pc P "Typing.boundName" [pc P "Typing.kwDecoded" []], pc P "Typing.tyT" []]
    let over (j : ℕ) : Option (List Tree → Term) :=
      if j = 5 then some fun Γ ↦ consT treeTy entry (W.qv 5 Γ) else none
    let pres (c : ℕ) (msg : String) (t : Term) (i : ℕ) (u : Bool) (k : Deducer)
        (inner : Bool := false) : Deducer :=
      W.present msg (fun Γ ↦
        if inner then W.inΓWith over (atPos c) Γ t else W.inΓ (atPos c) Γ t) i k u
    let srcTest (c : ℕ) : Term := if c = 0 then
        pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [v 4, v 0]), tyForm]
      else W.sourceTest
    let equalT ← primT Kernel.Prim.equal
    let childrenT ← primT Kernel.Prim.children
    let refuteTyping (msg : String) : Deducer := linkK K s!"decode: {msg} refuted" fun Γ Φ ψ ↦
      (K.hypFalse (W.hyp 6) Γ Φ ψ).orElse fun _ ↦ W.hypFalseU (W.hyp 6) Γ Φ ψ
    -- a type equal to another, by the equality's test decided: false refuting the typing; true
    -- the equation, by the equality's soundness
    let equalTy (msg : String) (x y : List Tree → Term) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ apps equalT [x Γ, y Γ]) (refuteTyping msg)
        (K.cutThm "equalSound" (fun Γ ↦ [x Γ]) <| K.allEΓ y <| K.impE (K.solve 3) <|
          normLastK K k)
    -- the position of the variable a present value's generalization introduced, its normal form
    let posOf (Γ : List Tree) (Φ : List Term) (t : Term) : ℕ :=
      match (((evalRw K.G K.E (K.rules Φ) .full Γ Φ (pc P "Prelude.get" [t])).map
          Prod.fst).getD t).label with
      | .var i => Γ.length - 1 - i
      | _ => 0
    -- the typing's tests, at the types generalized, the datatype, the decoded tree's type, the
    -- function's and the default's: the datatype's naming decided whole, then the types'
    -- equalities, as the typing's conjunction reads them; k at the positions of the datatype and
    -- of the function's result type
    let typingTests (k : ℕ → ℕ → Deducer) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let pD := posOf Γ₀ Φ₀ (W.inΓ (atPos 0) Γ₀ readTy)
      let pE := posOf Γ₀ Φ₀ (W.inΓ (atPos 1) Γ₀ tyT)
      let pG := posOf Γ₀ Φ₀ (W.inΓWith over (atPos 2) Γ₀ tyT)
      let pC := posOf Γ₀ Φ₀ (W.inΓWith over (atPos 3) Γ₀ tyT)
      (decideIn K (fun Γ ↦ pc P "Typing.namesData" [W.qv 4 Γ, atPos pD Γ,
          W.inΓ (atPos 0) Γ (typed tyForm)]) (refuteTyping "the naming") <|
        equalTy "the decoded tree's type" (atPos pE) (fun _ ↦ pc P "Typing.tyT" []) <|
        equalTy "the function's type" (atPos pG)
          (fun Γ ↦ pc P "Typing.tyArrow" [atPos pD Γ, atPos pC Γ]) (k pD pC)) Γ₀ Φ₀ ψ₀
    -- the typing's form of the type, the datatype's name's recognizer's name
    let f1 (Γ : List Tree) : Term := W.inΓ (atPos 0) Γ (typed tyForm)
    let rn (Γ : List Tree) : Term := recOfForm P (f1 Γ)
    let kwE : Term := pc P "Typing.kwDecoded" []
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    -- the conjunction last among the hypotheses split into its n parts
    let splitConj (n : ℕ) (k : Deducer) : Deducer :=
      (List.range (n - 1)).foldr (fun _ k ↦ K.conjE k) k
    -- the last hypothesis refuted by a negation among the hypotheses
    let byNeg : Deducer := fun Γ Φ ψ ↦
      let last := Φ.length - 1
      (List.range last).reverse.findSome? fun h ↦
        dImpE L h (K.byHyp last) (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    let nRes := (consCells ((nfE K.G K.E (K.rules []) [] (pc P "Reader.reservedNames" [])).getD
      Term.star)).length
    -- the naming's parts; the recognizer's name unequal to each reserved name
    -- the naming's parts split after the hypotheses of index n, each before the rest of the
    -- conjunction: the part of index i, from 0, at n + 2i + 1, the last at n + 10
    let partAt (n i : ℕ) : ℕ := if i < 5 then n + 2 * i + 1 else n + 10
    -- the naming's part of index i, after the hypotheses of index n, refuted: a negation by its
    -- antecedent's normalization, else by its own; else, by normalization, any hypothesis after
    -- index n; else any with the stage functions' steps unfolded, whose unfolding is costly
    let refuteAfter (n i : ℕ) : Deducer := fun Γ Φ ψ ↦
      let p := partAt n i
      let hs := (List.range (Φ.length - n)).map (n + ·)
      ((dImpE L p (K.solve 3) lastFalse Γ Φ ψ).orElse fun _ ↦ K.hypFalse p Γ Φ ψ).orElse fun _ ↦
        (hs.findSome? fun h ↦ K.hypFalse h Γ Φ ψ).orElse fun _ ↦
        hs.findSome? fun h ↦ W.hypFalseU h Γ Φ ψ
    -- the type's form an atom, so that the erasure's and the reader's steps at it read its
    -- characters: its node decided; at a list's or a checked node's label, the form, a source
    -- form, its own typing's form ({lit}`typedFixed`), refuting the naming's part that the typing's
    -- form is an atom; any other its being a source form, which tests its label alone; at the
    -- atoms' label, the characters fixed
    let typeAtom (n : ℕ) (k : Deducer) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦ do
      let x₀ := ((evalRw K.G K.E (K.rules Φ₀) .full Γ₀ Φ₀ (W.inΓ (atPos 0) Γ₀ tyForm)).map
        Prod.fst).getD Term.star
      let src := Φ₀.length
      let srcT := truth P.o (W.inΓ (atPos 0) Γ₀ (srcTest 0))
      let srcD ← linkK K "decode: the type's source form" (K.solve 3) Γ₀ Φ₀ srcT
      let refuted (bs : Option (List Bool)) : Deducer := fun Γ Φ ψ ↦
        if [some 2, some 13, some 14].contains (bs.map Oitavem.rank) then
          (K.cutThm "typedFixed" (fun Γ ↦ [W.inΓ (atPos 0) Γ tyForm]) <| K.allEΓ (W.qv 4) <|
            K.allEΓ (W.qv 7) <| K.impE (linkK K "decode: the type's typing form" fun Γ Φ ψ ↦
              (K.byHyp src Γ Φ ψ).orElse fun _ ↦ K.solve 3 Γ Φ ψ) <| normLastK K <|
            linkK K "decode: the type's typing form an atom" fun Γ Φ ψ ↦
              -- the label's equation, its test of equality with the atoms' label false
              K.image (partAt n 0) (fun t ↦ K.truthB (call D.eqB [] [t, numeral 1]))
                (K.trueOf (dFalse L dHyp)) Γ Φ ψ) Γ Φ ψ
        else dRwHyp (evalRw K.G K.E (K.rulesEx Φ src ++ [.thm (ix "srcNode") []]) .full) src
          (dFalse L dHyp) Γ Φ ψ
      -- at an atom, its characters, of position cs, fixed by the expansion of the numeral
      -- abbreviations, by its being a source form
      let chars (cs : ℕ) : Deducer := linkK K "decode: the type's characters" fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ src) .full) src
          (K.cutThm "charsFixedEq" (fun Γ ↦ [atPos cs Γ, W.qv 7 Γ])
            (K.impE (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ) k)) Γ Φ ψ
      dCut srcT srcD (K.treeNode x₀ (fun Γ Φ ψ ↦
        let cs := Γ.length - 1
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          if bs.map Oitavem.rank == some 1 then chars cs
          else linkK K s!"decode: the type's label {bs.map Oitavem.rank} refuted" (refuted bs))
        3 [] (v 1) Γ Φ ψ)) Γ₀ Φ₀ ψ₀
    -- the datatype's naming by the form, the datatype of position pD
    let namesDataT (pD : ℕ) (Γ : List Tree) : Term :=
      truth P.o (pc P "Typing.namesData" [W.qv 4 Γ, atPos pD Γ, f1 Γ])
    -- the naming kept as a hypothesis, which the equations later cut in leave out of the normal
    -- form its test was decided in, then its parts
    let parts (pD : ℕ) (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ do
      let φ := namesDataT pD Γ
      dCut φ (← linkK K "decode: the naming" (K.solve 3) Γ Φ φ) (fun Γ Φ ψ ↦
        let n := Φ.length
        (W.cutApply "namesDataParts" (fun Γ ↦ [f1 Γ, atPos pD Γ, W.qv 4 Γ]) [dHyp] <|
        splitConj 6 <| typeAtom n <|
        W.cutApply "reservedUnequal" (fun Γ ↦ [rn Γ]) [K.anyHyp] <| splitConj nRes (k n)) Γ Φ ψ)
        Γ Φ ψ
    -- the recognizer's name no numeral, as the reader reads it as written, by the naming's parts
    -- after the hypotheses of index n
    let recNumeral (n : ℕ) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome"
          [pc P "Reader.numeral" [call D.children [] [rn Γ]]])
        k (linkK K "decode: the recognizer a numeral" (refuteAfter n 4))
    -- the decoded tree's name not abbreviated, by the abbreviations' coherence with the keywords
    let decodedPlain (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [kwE, W.qv 7 Γ]]) k
        (linkK K "decode: the decoded tree's name abbreviated" <|
          dRwHyp (evalRw K.G K.E [.delta (T.q + 5 + 2 * nFolds)] .head) (W.hyp 9)
            (K.allEΓ (fun _ ↦ kwE) (K.impE (linkK K "decode: abbreviated, present" (K.solve 3))
              (K.impE (linkK K "decode: abbreviated, reserved" <|
                decideIn K (fun _ ↦ pc P "Prelude.isSome"
                  [pc P "Reader.indexOf" [kwE, pc P "Reader.reservedNames" []]])
                  (K.solve 3) (K.solve 3))
                (linkK K "decode: abbreviated, false" lastFalse)))))
    -- the recognizer's name not abbreviated, by the abbreviations' coherence with the environment
    let recPlain (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [rn Γ, W.qv 7 Γ]]) k
        (linkK K "decode: the recognizer abbreviated" <|
          dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) (W.hyp 2) fun Γ Φ ψ ↦
          dAllE L K.G K.E (Φ.length - 1) (rn Γ) (K.conjE fun Γ Φ ψ ↦
            dImpE L (Φ.length - 1) (K.solve 3) byNeg Γ Φ ψ) Γ Φ ψ)
    -- the recognizer's name not the decoded tree's, which is the implementation's
    let recUnbound (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ apps equalT [rn Γ, kwE]) k
        (linkK K "decode: the recognizer the decoded tree" <|
          K.cutThm "equalSound" (fun Γ ↦ [rn Γ]) <| K.allEΓ (fun _ ↦ kwE) <|
          K.impE (K.solve 3) fun Γ Φ ψ ↦
          K.image (Φ.length - 1) (fun t ↦ apps childrenT [t]) (fun Γ Φ ψ ↦ do
            let φ := truth P.o (pc P "implName" [rn Γ])
            dCut φ (← K.solve 3 Γ Φ φ) byNeg Γ Φ ψ) Γ Φ ψ)
    -- the recognizer's name in no scope of the context's names: there, the context gives it a
    -- type ({lit}`lookupAgreeB`), its antecedents the naming's parts and the abbreviation's test
    -- decided, so that it is one the typing admits as a binder's or the implementation's
    -- ({lit}`Typing.nameOk`), which a recognizer's name is not: the admission's tests decided,
    -- each true one leaving the implementation's, which the naming's parts refute, and all false
    -- refuting the recognizer's being the environment's ({name}`recognizerIn`)
    let recUnscoped (n : ℕ) (k : Deducer) : Deducer :=
      let part (i : ℕ) : Deducer := fun Γ Φ ψ ↦
        (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp (partAt n i) Γ Φ ψ
      decideIn K (fun Γ ↦ pc P "Prelude.isSome"
          [pc P "Reader.indexOf" [rn Γ, scopeOf P (W.qv 7 Γ) (W.qv 5 Γ)]]) k
        (linkK K "decode: the recognizer in scope" <|
          K.cutThm "lookupAgreeB" (fun Γ ↦ [W.qv 5 Γ]) <| K.allEΓ (W.qv 7) <|
          K.allEΓ (W.qv 4) <| K.allEΓ rn <| K.impE (W.byStmt 2) <|
          K.impE (linkK K "decode: in scope, no numeral" (part 4)) <|
          K.impE (linkK K "decode: in scope, not abbreviated" (dImpI L lastFalse)) <|
          K.impE (K.solve 3) <| K.conjE fun Γ Φ ψ ↦
          let found := Φ.length - 2
          dRwHyp (evalRw K.G K.E [.delta (T.q + 7 + 2 * nFolds)] .head) (W.hyp cxHyp)
            (K.allEΓ rn (K.impE (linkK K "decode: in scope, given a type" fun Γ Φ ψ ↦
              (K.solve 3 Γ Φ ψ).orElse fun _ ↦ K.byHyp found Γ Φ ψ) fun Γ Φ ψ ↦
              let ok := Φ.length - 1
              let refuteOk : Deducer := linkK K "decode: in scope, the implementation's"
                fun Γ Φ ψ ↦ dImpE L (partAt n 3) (K.byHyp ok) lastFalse Γ Φ ψ
              -- the recognizer of the datatype the form names, among the environment's
              (K.cutThm "recognizerIn" (fun Γ ↦ [pc P "Typing.envNoms" [W.qv 4 Γ]]) <|
                K.allEΓ (fun Γ ↦ nameOfForm P (f1 Γ)) <|
                K.impE (linkK K "decode: in scope, the name declared" (part 1)) fun Γ Φ ψ ↦
              let recIn := Φ.length - 1
              let tests : List (List Tree → Term) :=
                (["Typing.kwRep", "Typing.kwDecode", "Typing.kwDatum", "Reader.kwUnitValue"].map
                  fun kw Γ ↦ apps equalT [rn Γ, pc P kw []]) ++
                [fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf"
                    [rn Γ, pc P "Reader.primNames" []]],
                  fun Γ ↦ pc P "Typing.isRecognizer" [pc P "Typing.envNoms" [W.qv 4 Γ], rn Γ]]
              tests.foldr (fun t k ↦ decideIn K t k refuteOk)
                (linkK K "decode: in scope, the recognizer" (K.hypFalse recIn)) Γ Φ ψ) Γ Φ ψ))
          Γ Φ ψ)
    -- the annotation's kernel type, the reader's of the erasure's annotation
    let annK (Γ : List Tree) : Term := pc P "Prelude.get"
      [pc P "Reader.readType" [W.qv 6 Γ, pc P "Datatype.aT" []]]
    -- the statement's variables in the decoded tree's scope: the named context extended by its
    -- entry, the kernel's context by the annotation's kernel type
    let overK (j : ℕ) : Option (List Tree → Term) :=
      if j = 2 then some fun Γ ↦ consT treeTy (annK Γ) (W.qv 2 Γ) else over j
    let (_, kT) := datatypeTerms P (v nQ)
    let inner (c : ℕ) (t : Term) (Γ : List Tree) : Term := W.inΓWith overK (atPos c) Γ t
    -- the resolutions, as the reader tests them: the recognizer's index among the definitions'
    -- names, which the recognizers' hypothesis gives, the function's and the default's in the
    -- decoded tree's scope, then the tree's; then the kernel's types, the function's and the
    -- default's in its context extended; any absent refuting the statement's hypothesis; k at
    -- the position of the index, of the hypothesis of the recognizer at it and of the elements'
    -- generalized resolutions
    -- the reader's lookups in the scopes it extends, by their equations at a construction
    let WS : KwKit := { W with K := { K with more := K.more ++ lookupEqNames } }
    -- the stage functions' equations at the keywords of the expansion, a let over a test
    let WU : KwKit := { WS with K := { WS.K with more := WS.K.more ++
      (([("Reader.kwLet", 4), ("Reader.kwIf", 3)].flatMap fun (k, n) ↦
        (List.range nFolds).map fun j ↦ kwEqName k n j ++ "/decode").filter fun nm ↦
          0 < ix nm ∧ ix nm < E.size) } }
    -- a term generalized, its equation in the normal form by the rules of {lit}`WU`; k at the
    -- variable's position
    let genU (t : List Tree → Term) (k : ℕ → Deducer) : Deducer :=
      WS.generalize t fun Γ Φ ψ ↦
        let h := Φ.length - 1
        dRwHyp (evalRw K.G K.E (WU.K.rulesEx Φ h) .full) h (fun Γ Φ ψ ↦
          k (Γ.length - 1) Γ Φ ψ) Γ Φ ψ
    let formΓ (Γ : List Tree) : Term := Term.subst (kwForm P kw 4) fun i ↦ atPos (3 - i) Γ
    -- the equations among the hypotheses from index n in the normal form, after the
    -- hypotheses, but those whose written form exceeds a bound, whose normalization is costly
    let normHyps (n : ℕ) (k : Deducer) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      (List.range (Φ₀.length - n)).foldr (fun i k Γ Φ ψ ↦
        let t := Φ.getD (n + i) Term.star
        if (Internal.eqParts t).isNone || 4000 < (showT t).utf8ByteSize then k Γ Φ ψ else
        (dRwHyp (evalRw K.G K.E (WS.K.rulesEx Φ (n + i)) .full) (n + i) k Γ Φ ψ).orElse fun _ ↦
          k Γ Φ ψ) k Γ₀ Φ₀ ψ₀
    -- the resolution of the decoding, by the rules without the hypotheses, which pass the stages
    -- through the expansion's keywords while their atoms are as the equations state them, then
    -- by the rules, equal to it; that equation in the normal form by the rules, whose left side is
    -- the resolution's normal form by the rules
    let unfoldRes (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
      -- the equations whose right side contains their left side left out
      let contains (t : Term) (u : Term) : Bool :=
        RoseTree.para (fun l (cs : List (Term × Bool)) ↦
          RoseTree.node l (cs.map Prod.fst) == t || cs.any (·.2)) u
      let selfRef (j : ℕ) : Bool := match Internal.eqParts (Φ.getD j Term.star) with
        | some (l, r) => contains l r
        | none => false
      let rsAll := WU.K.rules Φ
      let rs := rsAll.filter fun r ↦ match r with
        | .hyp j => !selfRef j
        | _ => true
      -- the hypotheses that decide the keywords' abbreviations left out
      let jA := P.idx "Reader.lookupAbbrev"
      let mentionsA : Term → Bool := RoseTree.para fun l bs ↦
        (match l with
          | .defn j _ => j == jA
          | _ => false) || bs.any (·.2)
      -- and those of the numerals' abbreviations
      let iN := match (W.qv 7 Γ).label with
        | .var i => i
        | _ => 0
      let excluded (j : ℕ) : Bool :=
        mentionsA (Φ.getD j Term.star) || Term.occurs (Φ.getD j Term.star) iN
      let r₀ := rs.filter fun r ↦ match r with
        | .hyp j => !excluded j
        | _ => true
      let raw := W.inΓ formΓ Γ kT
      let (t₀, d₀, b₀) ← Internal.eval K.G K.E 0 r₀ 4096 .full Γ (rwHyps r₀ Φ) raw
      -- the atoms' expansions decided by the hypotheses, the reader's step folded: the rules but
      -- the equations at the resolution's fold, with the abbreviations' step unfolded
      let res4 := [("Reader.kwLet", 4), ("Reader.kwIf", 3)].map fun (k, n) ↦
        ix (kwEqName k n 4 ++ "/decode")
      let r₁ := (rs.filter fun r ↦ match r with
        | .thm j _ => !res4.contains j
        | _ => true) ++ [.delta (T.argIdx 3)]
      let (t₁, d₁, b₁) ← Internal.eval K.G K.E 0 r₁ 4096 .full Γ (rwHyps rs Φ) t₀
      -- then the reader's step and its case of lists unfolded
      let r₂ := rs ++ [.delta (T.argIdx 3), .delta (T.argIdx 4),
        .delta (P.idx "Reader.resolveList")]
      -- the reader's step at the nodes of the expansion, innermost first, each node's children's
      -- values in normal form before the step, which refers to them repeatedly, receives them
      let isStep (t : Term) : Bool := match t.label, t.children with
        | .app, [f, _] => match f.label, f.children with
          | .app, [g, _] => match g.label with
            | .defn j _ => j == T.argIdx 4
            | _ => false
          | _, _ => false
        | _, _ => false
      let (tW, d₂, b₂) ← reduceInnermost isStep
        (Internal.eval K.G K.E 0 r₂ 4096 .full Γ (rwHyps rs Φ)) t₁
      -- then the resolution at the top
      let (tU, d₃, b₃) ← Internal.eval K.G K.E 0 r₂ 4096 .full Γ (rwHyps rs Φ) tW
      let d := nd .join
        [(Internal.dTrans (d₀, b₀) (Internal.dTrans (d₁, b₁)
          (Internal.dTrans (d₂, b₂) (d₃, b₃)))).1, Internal.dRefl.1]
      -- the resolutions of the atoms the resolution meets, the decoded tree's name and the
      -- recognizer's, which its tests leave folded, each unfolded once by the rules, as equations
      let jA := P.idx "Reader.resolveAtom"
      let isAtomRes (t : Term) : Bool := match t.label, t.children with
        | .app, [f, _] => match f.label, f.children with
          | .app, [g, _] => match g.label, g.children with
            | .app, [e, _] => match e.label with
              | .defn j _ => j == jA
              | _ => false
            | _, _ => false
          | _, _ => false
        | _, _ => false
      -- an atom whose characters are closed is resolved by the reader's definitions unfolded,
      -- one whose characters are not by the rules and the statement's hypotheses
      let closedAt (a : Term) : Bool := match a.children with
        | [f, _] => match f.children with
          | [_, raw] => (freeVars raw Γ.length).isEmpty
          | _ => false
        | _ => false
      let atomEqs ← (collectOutside isAtomRes tU).mapM fun a ↦ do
        let (w, dw, _) ← Internal.eval K.G K.E 0
          (rs ++ [if closedAt a then .deltaBelow (jA + 1) [] else .delta jA]) 4096 .full Γ
          (rwHyps rs Φ) a
        pure (Term.eq a w, nd .join [dw, Internal.dRefl.1])
      -- the resolution's equation after them, in the normal form by the rules and them
      atomEqs.foldr (fun (φ, dφ) k Γ Φ ψ ↦ dCut φ dφ k Γ Φ ψ) (fun Γ Φ ψ ↦
        let h := Φ.length
        dCut (Term.eq raw tU) d (linkK K "decode: the resolution unfolded" <|
          dRwHyp (fun Γ Φ t ↦ evalRw K.G K.E (WS.K.rulesEx Φ h) .full Γ Φ t) h k) Γ Φ ψ) Γ Φ ψ
    -- an optional value decided present by its label's bits, which the unfolded resolution and
    -- the kernel's typing test, absent refuting the statement's hypothesis of index h; present,
    -- its value generalized
    let presentOpt (msg : String) (opt : List Tree → Term) (h : ℕ) (k : ℕ → Deducer) :
        Deducer :=
      decideOpt K opt
        (linkK K s!"decode: {msg} absent" (K.hypFalse h))
        (W.generalize (fun Γ ↦ pc P "Prelude.get" [opt Γ]) fun Γ Φ ψ ↦
          k (Γ.length - 1) Γ Φ ψ) (minimal := true)
    let presentVar (msg : String) (p : ℕ) (k : ℕ → Deducer) : Deducer :=
      presentOpt msg (atPos p) (W.hyp 7) k
    -- the kernel's types of the elements' resolutions: the statement's hypothesis of the resolved
    -- term's type with the typing folded, the resolved term's parts in the order the typing tests
    -- them ({name}`kernelOrder`), and {name}`decodeTypedThm` at them, its hypothesis that one
    -- with the typing folded, its conjunctions eliminated
    let jT := ix "typeInRr"
    -- the rules but the hypothesis h, the typing folded
    let foldedEx (Φ : List Term) (h : ℕ) : List Internal.NormRule :=
      (WS.K.rulesEx Φ h).filter fun r ↦ match r with
        | .thm j _ => j != jT
        | _ => true
    let kernelTypes (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      let h := W.hyp 8
      let folded (Φ : List Term) : List Internal.NormRule := foldedEx Φ h
      dRwHyp (fun Γ Φ t ↦ evalRw K.G K.E (folded Φ) .full Γ Φ t) h (fun Γ₁ Φ₁ ψ₁ ↦
        let lbl (n : ℕ) : Term :=
          ((evalRw K.G K.E (K.rules []) .full Γ₁ [] (numeral n)).map Prod.fst).getD Term.star
        -- the hypothesis rewritten, after the others
        let h₁ := Φ₁.length - 1
        let hT := Φ₁.getD h₁ Term.star
        match (match collectOutside (isTypeIn P) hT with
            | [ty] => typeInArgs ty
            | _ => none) with
        | some (G, ctx, R) =>
          let sh (Γ : List Tree) (t : Term) : Term :=
            Term.rename t (· + (Γ.length - Γ₁.length))
          let parts := ((kernelOrder lbl true R ctx).map (·.2.1)).toArray
          match parts[4]?, parts[7]?, parts[9]?, parts[10]? with
          | some A, some f, some c, some e =>
            W.cutApply "decodeTyped" (fun Γ ↦ [e, c, f, A, ctx, G].map (sh Γ))
              [fun Γ Φ ψ ↦ dRwBy (evalRw K.G K.E (folded Φ) .full) dHyp Γ Φ ψ]
              (K.conjE fun Γ Φ ψ ↦ (K.conjE k Γ Φ ψ).orElse fun _ ↦
                dConjE K.L (Φ.length - 2) k Γ Φ ψ) Γ₁ Φ₁ ψ₁
          | _, _, _, _ => dbgTrace "decode: the kernel's typing's parts absent" fun _ ↦ none
        | none => dbgTrace "decode: no kernel's typing" fun _ ↦ none)
        Γ Φ ψ
    -- an element's kernel type, its soundness's antecedent: a typing among the hypotheses, the
    -- latest first, in the normal form by the rules with the typing folded, the goal by it
    let typedK : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦
        if (collectOutside (isTypeIn P) (Φ.getD h Term.star)).isEmpty then none else
        dRwHyp (fun Γ Φ t ↦ evalRw K.G K.E (foldedEx Φ h) .full Γ Φ t) h (fun Γ Φ ψ ↦
          dRwBy (evalRw K.G K.E (foldedEx Φ (Φ.length - 1)) .full) dHyp Γ Φ ψ) Γ Φ ψ
    let anteK (i : ℕ) : Option Deducer := if i = 8 then some typedK else none
    let resolutions (n : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → Deducer) : Deducer :=
      dRwHyp (evalRw K.G K.E [.delta (T.q + 6 + 2 * nFolds)] .head) (W.hyp 11) <|
      K.allEΓ (fun Γ ↦ nameOfForm P (f1 Γ)) <|
      K.impE (linkK K "decode: the recognizer's datatype" K.anyHyp) <| K.exE <| K.conjE
        fun Γ Φ ψ ↦
      let e := Φ.length - 2
      let rh := Φ.length - 1
      let pj := Γ.length - 1
      linkK K "decode: the recognizer's index normalized" (
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ e) .full) e (
      -- no keyword the reader reads names the function's erasure, the head of its application
      -- to the decoded tree ({name}`srcHeadFree`), in the decoded tree's context
      W.cutApply "srcHeadFree" (fun Γ ↦ [atPos 2 Γ, consT treeTy entry (W.qv 5 Γ), W.qv 4 Γ,
          W.qv 7 Γ, W.qv 3 Γ])
        [W.byStmt 2, K.solve 3, K.solve 3, K.solve 3] <|
      splitConj readerKeywords.length <|
      -- the elements' resolutions and the annotation's type generalized, then the resolution's
      -- equation with its normal form, the stage functions' steps unfolded, in which the
      -- reader's steps meet them as variables; each decided present, in the order the
      -- resolution's binds test them, the function's first
      genU (inner 2 kT) fun pF ↦ genU (inner 3 kT) fun pC ↦
      genU (fun Γ ↦ W.inΓ (atPos 1) Γ kT) fun pE ↦
      normHyps n <|
      unfoldRes <|
      presentVar "the function's resolution" pF fun gF ↦
      presentVar "the default's resolution" pC fun gC ↦
      presentVar "the tree's resolution" pE fun gE ↦
      kernelTypes <|
      k pj rh gF gC gE)) Γ Φ ψ
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let tyTT : Term := pc P "Typing.tyT" []
    -- the soundness at the element of position c, the function or the default, at any value x
    -- related at the tree type: in the decoded tree's scope, the environment extended by x,
    -- related to the named context extended ({lit}`envTCons`), whose names the typing admits, the
    -- decoded tree's the implementation's ({lit}`cxTCons`), decided whether the typing admits it
    -- as a binder's, the environment unknown
    let atValue (c : ℕ) : Deducer := dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let x := atPos (Γ₁.length - 1)
      let rel := Φ₁.length - 1
      let overX (j : ℕ) : Option (List Tree → Term) :=
        if j = 9 then some fun Γ ↦ consT treeTy (x Γ) (W.qv 9 Γ) else overK j
      let envOk : Deducer := W.cutApply "envTCons"
        (fun Γ ↦ [x Γ, entry, W.qv 9 Γ, W.qv 5 Γ, W.qv 10 Γ]) [K.byHyp (W.hyp 1), K.byHyp rel]
        byLast
      let nm : Term := pc P "Typing.boundName" [kwE]
      let cons : Deducer := W.cutApply "cxTCons" (fun Γ ↦ [tyTT, nm, W.qv 4 Γ, W.qv 5 Γ])
        [K.solve 3, K.byHyp (W.hyp cxHyp)] byLast
      let cxOk : Deducer := linkK K "decode: the context's names" <|
        decideIn K (fun Γ ↦ pc P "Typing.nameOk" [W.qv 4 Γ, nm]) cons cons
      W.soundAtWith anteK c overX envOk cxOk byLast Γ₁ Φ₁ ψ₁
    -- the recognizer's reference, at any value related at the tree type, converging to a
    -- function deciding membership: the recognizers' hypothesis at the datatype's name, of
    -- position rh, the definition's evaluation's threshold and value, a level below the
    -- reference's
    let recognizerAt (rh : ℕ) : Deducer := dAllI L <| dImpI L <|
      linkK K "decode: the recognizer" <|
      (fun k Γ Φ ψ ↦ dExE L K.G K.E rh k Γ Φ ψ) <| K.conjE fun Γ₂ Φ₂ ψ₂ ↦
        let e := Φ₂.length - 2
        K.unfoldConv (K.exE (K.exE (K.conjE fun Γ Φ ψ ↦
          let st := Φ.length - 2
          let r := Φ.length - 1
          let n := v (Γ.length - Γ₂.length - 1)
          let w := v (Γ.length - Γ₂.length - 2)
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ e) .full) e (K.norm (dConv L K.G K.E S (succN n) w
            (linkK K "decode: the recognizer stable" fun Γ Φ ψ ↦
              dAllE L K.G K.E st (v 0) (fun Γ Φ ψ ↦
                dRwHyp (evalRw K.G K.E (K.rules Φ.dropLast) .full) (Φ.length - 1)
                  K.byNorm Γ Φ ψ) Γ Φ ψ)
            (linkK K "decode: the recognizer related" (K.byHyp r)))) Γ Φ ψ))) Γ₂ Φ₂ ψ₂
    -- a member's quotation related at the datatype ({lit}`relTDatum`), the naming the hypothesis
    -- the naming's parts keep
    let memberAt (pD : ℕ) : Deducer := dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let t := atPos (Γ₁.length - 1)
      let member := Φ₁.length - 1
      linkK K "decode: a member" (W.cutApply "relTDatum"
        (fun Γ ↦ [t Γ, f1 Γ, atPos pD Γ, W.qv 4 Γ, W.qv 10 Γ])
        [linkK K "decode: a member's markers" (W.byStmt 10),
          linkK K "decode: a member's naming" dHyp,
          linkK K "decode: a member's membership" (K.byHyp member)] byLast) Γ₁ Φ₁ ψ₁
    -- the binding the application of the abstraction of the conditional to the tree's term
    -- ({lit}`appCompat`), the abstraction by {lit}`lamCompat`, its body by {name}`decodeBody`,
    -- the tree by its soundness; the form the atom of its characters ({name}`atomEta`), as the
    -- recognizers' membership names it
    let eval (pD pC pj rh pF pK pE : ℕ) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let A (Γ : List Tree) : Term := nodeT (Term.pair (numeral Kernel.Label.ref)
        (consT treeTy (atPos pj Γ) (nilT treeTy)))
      let body (Γ : List Tree) : Term :=
        condK (appT (A Γ) var0T) (appT (atPos pF Γ) var0T) (atPos pK Γ)
      (linkK K "decode: the evaluation" <|
        W.cutApply "atomEta" (fun Γ ↦ [f1 Γ]) [K.solve 3] <| normLastK K <|
        K.cutThm "appCompat" (fun Γ ↦ [W.qv 9 Γ, atPos pE Γ, lamT (annK Γ) (body Γ), atPos pC Γ,
          tyTT, W.qv 10 Γ]) <|
        K.impE (linkK K "decode: the abstraction" <|
          K.cutThm "lamCompat" (fun Γ ↦ [W.qv 9 Γ, body Γ, annK Γ, atPos pC Γ, tyTT,
            W.qv 10 Γ]) <|
          K.impE (linkK K "decode: the body" <|
            W.cutApply "decodeBody" (fun Γ ↦ [W.qv 9 Γ, atPos pF Γ, atPos pK Γ, A Γ,
              nameOfForm P (f1 Γ), atPos pD Γ, atPos pC Γ, W.qv 10 Γ])
              [linkK K "decode: the function" (atValue 2),
                linkK K "decode: the default" (atValue 3), recognizerAt rh, memberAt pD] <|
            linkK K "decode: the body's conclusion" byLast) <|
          linkK K "decode: the abstraction's conclusion" byLast) <|
        K.impE (linkK K "decode: the tree" <|
          W.soundAtWith anteK 1 (fun _ ↦ none) (fun _ _ _ ↦ none) (fun _ _ _ ↦ none) byLast) <|
        linkK K "decode: the conclusion" byLast) Γ₀ Φ₀ ψ₀
    -- the reader's reading of the erasure, the datatype of position pD, the result type of pC
    let reader (pD pC : ℕ) : Deducer :=
      parts pD fun n ↦ decodedPlain <| recPlain <| recUnbound <|
      recUnscoped n <| recNumeral n <| resolutions n (eval pD pC)
    let chain : Deducer :=
      -- the keywords the erasure writes not abbreviated
      W.plainKw "Reader.kwLet" (reservedK K "Reader.kwLet") <|
      W.plainKw "Reader.kwIf" (reservedK K "Reader.kwIf") <|
      W.plainKw "Reader.kwT" (reservedK K "Reader.kwT") <|
      (List.range 4).foldr (fun c k ↦
        pres c s!"expansion {c}" (pc P "Datatype.expandExpr" [v 7, v nQ]) 5 true k) <|
      (W.sources · srcTest) <| (W.unfold · 1) <|
      pres 0 "the type" readTy 6 false <|
      pres 1 "the tree's type" tyT 6 false <|
      pres 2 "the function's type" tyT 6 false (inner := true) <|
      pres 3 "the default's type" tyT 6 false (inner := true) <|
      K.norm <| typingTests reader
    let some d := (List.range nQ).foldr (fun _ k ↦ dAllI L k)
        ((List.range W.nH).foldr (fun _ k ↦ dImpI L k) (verifyK K "decode" <| chain))
        a.ctx a.hyps a.concl
      | dbgTrace s!"{kw}: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness at decodings: the lemmas and the stage functions' equations
at a decoding, the tests of {name}`decodeTests` folded. -/
def decodeDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [srcHeadFree P S T, recognizerIn P S, indexAbsent P S, reservedUnequal P S,
    namesDataParts P S T, decodeBody P S T, decodeTyped P S] ++
    kwEqs { P with folded := P.folded ++ decodeTests } T "Typing.kwDecode" 4

/-- The names of the declarations the development at decodings follows: the base's, the atom's,
the list's, the stages', the applications', the expansion's and the assembly's. -/
def decodeAfter (P : Prog) (S : Defs) (T : Defs3) : Option (List String) := do
  let names ← listNames P S T
  pure (names ++ (stagesDev3 P S T).map (·.1) ++ (applyDev3 P S T).map (·.1) ++
    (expansionDev3 P S T).map (·.1) ++ (assemblyDev3 P S T).map (·.1))

/-- The development at decodings ({name}`decodeDev3`), after the declarations of
{name}`decodeAfter`, stored as the certificate {lit}`datatype-decode`. -/
def decodeCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := decodeAfter P S T | throw "the base is not stated"
  certifyAfter P names "datatype-decode" (decodeDev3 P S T) before

/-- The soundness at decodings after the declarations of {name}`decodeAfter`, the datum's and
the development at decodings. -/
def decodeCaseCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := decodeAfter P S T | throw "the base is not stated"
  certifyAfter P (names ++ (datumDev3 P S T).map (·.1) ++ (decodeDev3 P S T).map (·.1))
    "decode-case" ([atomEta P S, mapAppend P S T, mapAppendEq P S T] ++ expansionEqs P T ++
      [decodeCase P S T])
    before

end GebTests.Prototypes.FreeTopos.Datatypes

end
