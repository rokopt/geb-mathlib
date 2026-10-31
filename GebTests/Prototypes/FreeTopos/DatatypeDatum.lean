/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeApply
public meta import GebTests.Prototypes.FreeTopos.DatatypeData -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at datums

The soundness of the datatype language's stage-1 compiler
({lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`) at a datatype's datum, the quotation of a tree
the typing checks to be a member. The typing reads the datum's form as a tree of atoms, none naming
a numeral abbreviation, and lists headed by a numeral ({lit}`Typing.plainDatum`); the erasure and
the expansion of numeral abbreviations leave such a form unchanged ({lit}`datumFixed`), by
induction on rose trees, so that the reader quotes the tree the typing checked. The typing's tests
of a datum are kept folded, each opened by its equations one step at a time.

## Main definitions

* {lit}`mapFixed` — a map fixing each element of a list fixes the list.
* {lit}`datumAll` — the children of a datum fixed, given that each child is.
* {lit}`datumFixed` — the erasure and the expansion of numeral abbreviations fix a datum.
* {lit}`typedFixed` — the typing's form of a source form is the form.
* {lit}`relTDatum` — a member's quotation is related at the datatype a form names.
* {lit}`datumCase` — the soundness at a datum.

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

/-- The typing's tests of a datum, which the proofs keep folded. -/
def datumTests : List String :=
  ["Typing.plainDatum", "Typing.datumAtom", "Typing.datumKids", "Typing.datumList"]

/-- The typing's tests at a datum and the reader's reading of it, which the soundness at a datum
decides whole: the tests of {name}`datumTests`, the membership, the naming of the datatype and the
reading. -/
def datumCaseTests : List String :=
  datumTests ++ ["Typing.memberOf", "Typing.namesData", "Reader.readDatum"]

/-- The kit of the proofs at datums: the typing's tests of a datum folded, the further equations
{lit}`more` used as rules. -/
def datumKit (P : Prog) (S : Defs) (ix : String → ℕ) (E : Array Internal.Entry)
    (more : List String) : Kit :=
  ⟨{ P with folded := P.folded ++ datumTests }, S, E, ix, more⟩

/-- The map of a function of the trees, in the context after the list's step's two variables,
over a list. -/
def mapT (f : Term → Term) (xs : Term) : Term :=
  Term.listRec (nilT treeTy) (consT treeTy (f (v 1)) (v 0)) xs

/-- The vocabulary of the typing's fold of a datum, the first further fold
({name}`GebTests.Prototypes.FreeTopos.Datatypes.auxFoldSpecs`): its fusion with its definition's
map, its definition at a node, its rebuilding, the test in terms of its fold, and its first
components at the children. -/
def datumVocab (P : Prog) (T : Defs3) : List Step :=
  foldVocab P T nFolds .step ++ [foldDefEq P T nFolds, kidsEq P T nFolds .list]

/-- The names of the vocabulary of the typing's fold of a datum used as rules. -/
def datumVocabNames : List String :=
  [s!"fold{nFolds}Def", s!"fold{nFolds}Node", s!"fold{nFolds}Fst", s!"fold{nFolds}Kids",
    "pdValues"]

/-- An equation of the tests of a datum, in a context, proved by normalizing both sides with the
definitions of the indices {lit}`unfold` unfolded and the other tests folded, the fold's
vocabulary among the rules. -/
def datumEq (P : Prog) (S : Defs) (name : String) (Γ : List Tree) (t u : Term)
    (unfold : List ℕ) : Step :=
  (name, fun ix E ↦ do
    let K := datumKit P S ix E (datumVocabNames.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size)
    let rs := K.rules [] ++ unfold.map .delta
    let some l := nfE K.G E (K.rules []) Γ t | dbgTrace s!"{name}: left" fun _ ↦ none
    let some r := nfE K.G E (K.rules []) Γ u | dbgTrace s!"{name}: right" fun _ ↦ none
    let some d := byMode .full K.G E 0 rs Γ [] l r
      | dbgTrace s!"{name}: unequal {(firstDiff l r).map fun (a, b) ↦
          s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The argument of an application. -/
def appArg (t : Term) : Option Term := match t.label, t.children with
  | .app, [_, x] => some x
  | _, _ => none

/-- The values of the typing's fold of a datum at a list's children, as its cases read them, the
map of the test over the children: the arguments of the lists' tests at the two sides of
{lit}`pdList`, each in normal form with the fold's cases unfolded, equal by induction on the
children. -/
def pdValues (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("pdValues", fun ix E ↦ do
    let K := datumKit P S ix E (datumVocabNames.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size)
    let Γ := [list treeTy, T.envTy]
    let rs := K.rules [] ++ [.delta (T.argIdx nFolds)]
    let some l := nfE K.G E rs Γ
        (pc P "Typing.plainDatum" [v 1, nodeT (Term.pair (numeral 2) (v 0))]) >>= appArg
      | dbgTrace "pdValues: left" fun _ ↦ none
    let some r := nfE K.G E rs Γ (pc P "Typing.datumList"
        [mapT (fun c ↦ pc P "Typing.plainDatum" [v 3, c]) (v 0)]) >>= appArg
      | dbgTrace "pdValues: right" fun _ ↦ none
    let some d := Internal.byListIndHyp K.G E 0 0 1 rs 4096 Γ [] l r
      | dbgTrace s!"pdValues: {showT l}\n  = {showT r}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The equations of the tests of a datum: the children's test at the empty list and at a
construction, the test of a datum at an atom and at a list, its fold's cases unfolded. -/
def datumEqs (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let and2 (a b : Term) : Term := pc P "Prelude.and" [a, b]
  let node (k : ℕ) : Term := nodeT (Term.pair (numeral k) (v 0))
  [datumEq P S "kidsNil" [] (pc P "Typing.datumKids" [nilT treeTy]) (leafT (numeral 1))
      [P.idx "Typing.datumKids"],
    datumEq P S "kidsCons" [list treeTy, treeTy]
      (pc P "Typing.datumKids" [consT treeTy (v 1) (v 0)])
      (and2 (v 1) (pc P "Typing.datumKids" [v 0])) [P.idx "Typing.datumKids"],
    datumEq P S "pdAtom" [list treeTy, T.envTy] (pc P "Typing.plainDatum" [v 1, node 1])
      (pc P "Typing.datumAtom" [v 1, v 0]) [T.argIdx nFolds],
    pdValues P S T,
    datumEq P S "pdList" [list treeTy, T.envTy] (pc P "Typing.plainDatum" [v 1, node 2])
      (pc P "Typing.datumList" [mapT (fun c ↦ pc P "Typing.plainDatum" [v 3, c]) (v 0)])
      [T.argIdx nFolds]]

/-- A function of trees fixing each element of a list fixes the list: the map of the function over
the list is the list; by induction on the list, the head fixed and the rest by the induction
hypothesis. -/
def mapFixed (P : Prog) (S : Defs) : Step :=
  ("mapFixed", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let F := exp treeTy treeTy
    -- under the function v0, the list v1
    let φ := Internal.Logic.all P.o F (Term.lam F (Internal.Logic.imp P.o
      (S.allL (Term.lam treeTy (Term.eq (Term.app (v 1) (v 0)) (v 0))) (v 1))
      (Term.eq (mapT (fun c ↦ Term.app (v 2) c) (v 1)) (v 1))))
    let d₀ ← dAllI L (dImpI L (K.solve 2)) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a construction: the head fixed, the rest's map by the induction hypothesis
    let cons : Deducer := dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let hA := Φ₁.length - 1
      let f (Γ : List Tree) : Term := v (Γ.length - Γ₁.length)
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₁ hA) .full) hA (K.conjE fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (f Γ) (K.impE (K.byHyp (Φ.length - 1)) (K.solve 3)) Γ Φ ψ) Γ₁ Φ₁ ψ₁)
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The test of source forms at the expansion of the numeral abbreviations {lit}`nums`, at a
tree, as the statement takes it of the form. -/
def srcAt (P : Prog) (nums x : Term) : Term :=
  truth P.o (pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [Term.rename nums (· + 1),
    v 0]), x])

/-- The formula that the erasure and the expansion of numeral abbreviations fix a datum, at the
tree of index 0: at every typing environment and abbreviations coherent with it, a source form
whose atoms' characters the expansion fixes and which the typing reads as a datum
({lit}`Typing.plainDatum`) is its own erasure and its own expansion. -/
def datumφ (P : Prog) (T : Defs3) : Term :=
  -- under the abbreviations v0, the environment v1, the tree v2
  Internal.Logic.all P.o T.envTy (Term.lam T.envTy (Internal.Logic.all P.o (list treeTy)
    (Term.lam (list treeTy) (Internal.Logic.imp P.o (T.numsT (v 1) (v 0))
      (Internal.Logic.imp P.o (srcAt P (v 0) (v 2))
      (Internal.Logic.imp P.o (truth P.o (pc P "Typing.plainDatum" [v 1, v 2]))
        (Internal.Logic.conj P.o (Term.eq (pc P "Datatype.eraseExpr" [v 2]) (v 2))
          (Term.eq (pc P "Reader.expandNums" [v 0, v 2]) (v 2)))))))))

/-- The test of source forms at a list split at its head: the head's test and the rest's, in the
context of the rest, the head and the abbreviations. -/
def srcCons (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("srcCons", fun ix E ↦ do
    let K := datumKit P S ix E (vocab3.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size)
    let Γ := [list treeTy, treeTy, list treeTy]
    let src (x : Term) : Term := pc P "srcForm"
      [Term.lam treeTy (pc P "Reader.expandNums" [v 3, v 0]), x]
    let l := src (nodeT (Term.pair (numeral 2) (consT treeTy (v 1) (v 0))))
    let r := pc P "Prelude.and" [src (v 1), src (nodeT (Term.pair (numeral 2) (v 0)))]
    let rs := K.rules [] ++ [.delta (T.argIdx 5)]
    let some l' := nfE K.G E (K.rules []) Γ l | dbgTrace "srcCons: left" fun _ ↦ none
    let some r' := nfE K.G E (K.rules []) Γ r | dbgTrace "srcCons: right" fun _ ↦ none
    let some d := byMode .full K.G E 0 rs Γ [] l' r'
      | dbgTrace s!"srcCons: unequal {(firstDiff l' r').map fun (a, b) ↦
          s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l' r'⟩, d))

/-- The test of source forms at a checked node of the label given, the list's test at its
children, in the context of the children and the abbreviations. -/
def srcChecked (P : Prog) (S : Defs) (T : Defs3) (label : ℕ) : Step :=
  (s!"srcChecked{label}", fun ix E ↦ do
    let K := datumKit P S ix E (vocab3.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size)
    let Γ := [list treeTy, list treeTy]
    let src (l : ℕ) : Term := pc P "srcForm"
      [Term.lam treeTy (pc P "Reader.expandNums" [v 2, v 0]), nodeT (Term.pair (numeral l) (v 0))]
    let rs := K.rules [] ++ [.delta (T.argIdx 5)]
    let some l' := nfE K.G E (K.rules []) Γ (src label) | dbgTrace "srcChecked: left" fun _ ↦ none
    let some r' := nfE K.G E (K.rules []) Γ (src 2) | dbgTrace "srcChecked: right" fun _ ↦ none
    let some d := byMode .full K.G E 0 rs Γ [] l' r'
      | dbgTrace s!"srcChecked: unequal {(firstDiff l' r').map fun (a, b) ↦
          s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l' r'⟩, d))

/-- The children of a node fixed: where each child is fixed ({lit}`datumφ`), the list of the
children is a source form and the typing reads each as a datum ({lit}`Typing.datumKids`), the maps
of the erasure and of the expansion of numeral abbreviations over the children are the children;
by induction on the list, the head's tests decided, then the rest's, false refuted; the head fixed
by its soundness, the rest by the induction hypothesis. -/
def datumAll (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("datumAll", fun ix E ↦ do
    let K := datumKit P S ix E
      ((vocab3 ++ ["kidsNil", "kidsCons", "srcCons"]).filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size)
    let L := K.L
    let o := P.o
    -- under the abbreviations v0, the environment v1, the list v2
    let kidsT (env xs : Term) : Term := pc P "Typing.datumKids"
      [mapT (fun c ↦ pc P "Typing.plainDatum" [Term.rename env (· + 2), c]) xs]
    let listOf (xs : Term) : Term := nodeT (Term.pair (numeral 2) xs)
    let ψ := Internal.Logic.imp o (S.allL (Term.lam treeTy (datumφ P T)) (v 0))
      (Internal.Logic.all o T.envTy (Term.lam T.envTy (Internal.Logic.all o (list treeTy)
        (Term.lam (list treeTy) (Internal.Logic.imp o (T.numsT (v 1) (v 0))
          (Internal.Logic.imp o (srcAt P (v 0) (listOf (v 2)))
          (Internal.Logic.imp o (truth o (kidsT (v 1) (v 2)))
            (Internal.Logic.conj o
              (Term.eq (mapT (fun c ↦ pc P "Datatype.eraseExpr" [c]) (v 2)) (v 2))
              (Term.eq (mapT (fun c ↦ pc P "Reader.expandNums" [v 2, c]) (v 2)) (v 2))))))))))
    let some d₀ := dImpI L (dAllI L (dAllI L (dImpI L (dImpI L (dImpI L
        (linkK K "datumAll: nil" (K.solve 3))))))) [] []
      (Term.subst ψ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "datumAll: nil" fun _ ↦ none
    -- a construction: hypotheses the induction hypothesis, the construction's soundness, the
    -- coherence, the source forms' test, the children's test; the head's tests and the rest's
    -- decided, false refuted
    let cons : Deducer := dImpI L (dAllI L (dAllI L (dImpI L (dImpI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      -- each universal introduction appends truth
      let hAll := Φ₁.length - 6
      let hNums := Φ₁.length - 3
      let hSrc := Φ₁.length - 2
      let hKids := Φ₁.length - 1
      let nums (Γ : List Tree) : Term := v (Γ.length - Γ₁.length)
      let env (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + 1)
      let tail (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + 2)
      let head (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + 3)
      let src (Γ : List Tree) (x : Term) : Term := pc P "srcForm"
        [Term.lam treeTy (pc P "Reader.expandNums" [Term.rename (nums Γ) (· + 1), v 0]), x]
      let refute (h : ℕ) : Deducer := linkK K "datumAll: refute" fun Γ Φ ψ ↦ K.hypFalse h Γ Φ ψ
      (linkK K "datumAll: cons" <|
      decideIn K (fun Γ ↦ src Γ (head Γ)) (refute hSrc) <|
      decideIn K (fun Γ ↦ src Γ (listOf (tail Γ))) (refute hSrc) <|
      decideIn K (fun Γ ↦ pc P "Typing.plainDatum" [env Γ, head Γ]) (refute hKids) <|
      decideIn K (fun Γ ↦ kidsT (env Γ) (tail Γ)) (refute hKids) <|
      -- the head fixed, by its soundness; the rest's maps by the induction hypothesis
      linkK K "datumAll: decided" fun Γ₂ Φ₂ ψ₂ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₂ hAll) .full) hAll (linkK K "datumAll: split" <|
      K.conjE fun Γ Φ ψ ↦
        let hHead := Φ.length - 2
        let hRest := Φ.length - 1
        dAllE L K.G K.E hHead (env Γ) (K.allEΓ nums (K.impE (K.byHyp hNums)
          (K.impE (linkK K "datumAll: head's source" (K.solve 3))
          (K.impE (linkK K "datumAll: head" (K.solve 3)) (K.conjE fun Γ Φ ψ ↦
          dImpE L 0 (K.byHyp hRest) (K.allEΓ env (K.allEΓ nums (K.impE (K.byHyp hNums)
            (K.impE (linkK K "datumAll: rest's source" (K.solve 3))
            (K.impE (linkK K "datumAll: rest" (K.solve 3))
              (K.conjE (linkK K "datumAll: maps" (K.solve 3)))))))) Γ Φ ψ))))) Γ Φ ψ) Γ₂ Φ₂ ψ₂)
        Γ₁ Φ₁ ψ₁)))))
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem ψ] (Internal.listConsAt 1 treeTy ψ)
    pure (⟨0, [list treeTy], [], ψ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- An equation of two lists of the children of index 0, the second the map of a stage function,
proved by induction on the children, each side in normal form by the datatype language's
vocabulary. -/
def valuesEq (P : Prog) (S : Defs) (name : String) (Γ : List Tree) (t u : Term) : Step :=
  (name, fun ix E ↦ do
    let K := datumKit P S ix E (vocab3.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size)
    let rs := K.rules []
    let some l := nfE K.G E rs Γ t | dbgTrace s!"{name}: left" fun _ ↦ none
    let some r := nfE K.G E rs Γ u | dbgTrace s!"{name}: right" fun _ ↦ none
    let some d := Internal.byListIndHyp K.G E 0 0 1 rs 4096 Γ [] l r
      | dbgTrace s!"{name}: {showT l}\n  = {showT r}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The children's values as the erasure's and the expansion of numeral abbreviations' steps read
them at a list, the maps of the stage functions over the children: the erasure's values forced by
the prelude's right fold, and the expansion's applied to the abbreviations. -/
def stageValues (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let th := exp one treeTy
  -- the erasure's fold's values, pairs of the rebuilt tree and the suspended erasure
  let pty := (Internal.typeIn P.G 0 [treeTy] (T.foldAt 2 [] (v 0))).getD treeTy
  let folds := Term.listRec (nilT pty) (consT pty (T.foldAt 2 [] (v 1)) (v 0)) (v 0)
  let forced : Term := foldrT th (list treeTy)
    (Term.lam th (Term.lam (list treeTy) (consT treeTy (Term.app (v 1) Term.star) (v 0))))
    (nilT treeTy) (Term.listRec (nilT th) (consT th (Term.snd (v 1)) (v 0)) folds)
  let applied : Term := Term.app (Term.listRec (Term.lam (list treeTy) (nilT treeTy))
    (Term.lam (list treeTy) (consT treeTy (T.foldAt 3 [v 0] (v 2)) (Term.app (v 1) (v 0))))
    (v 0)) (v 1)
  [valuesEq P S "eraseValues" [list treeTy] forced
      (mapT (fun c ↦ pc P "Datatype.eraseExpr" [c]) (v 0)),
    valuesEq P S "numsValues" [list treeTy, list treeTy] applied
      (mapT (fun c ↦ pc P "Reader.expandNums" [v 3, c]) (v 0))]

/-- The keywords of the forms the erasure rewrites, as its tests name them. -/
def erasedKeywords : List String := ["Datatype.kwRep", "Datatype.kwDecode", "Datatype.kwDatum"]

/-- The erasure and the expansion of numeral abbreviations fix a datum ({lit}`datumφ`), by
induction on rose trees, the hypothesis of induction the formula at every child: the node's label
decided. At an atom, the erasure is the atom; its name abbreviated, the coherence gives the
environment's numeral name, at which the typing's test is false. At a list, the test's head and
children decided, the children fixed ({name}`datumAll`) and the stage functions' values the maps
over them ({lit}`eraseValues`, {lit}`numsValues`); the head a numeral's atom, else the test
refuted, whose name no keyword the erasure rewrites names, a keyword's characters being no
numeral's. At a node of another label the test is false. -/
def datumFixed (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("datumFixed", fun ix E ↦ do
    let proved (nms : List String) : List String := nms.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size
    let more := proved (vocab3 ++ datumVocabNames ++ ["pdAtom", "pdList", "kidsNil", "kidsCons"])
    let K := datumKit P S ix E more
    -- at a list, the stage functions' values as maps over the children
    let KL := datumKit P S ix E (more ++ proved ["eraseValues", "numsValues"])
    let L := K.L
    let φ := datumφ P T
    let childrenT ← primT Kernel.Prim.children
    let unfoldTests : List Internal.NormRule :=
      (["Typing.datumAtom", "Typing.datumList"].map P.idx ++ [T.argIdx nFolds]).map .delta
    -- a hypothesis normalized with the tests unfolded, its bits decided, false cases refuted
    let splitTests (h : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ unfoldTests) .full) h
        (K.splitHyp (Φ.length) k 8) Γ Φ ψ
    let refuteAny : Deducer := linkK K "datumFixed: refuted" (anyFalse K)
    -- the head's characters a keyword's, the test of an atom refuted: its name's being a
    -- numeral abbreviation's decided, then some hypothesis normalized to falsity with the reader's
    -- numerals and the test computed, the last first
    let refuteNumeral (env cs : List Tree → Term) : Deducer :=
      let byNumeral : Deducer := fun Γ Φ ψ ↦
        (List.range Φ.length).reverse.findSome? fun h ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ unfoldTests ++
              [.delta (P.idx "Reader.numeral"), .delta (P.idx "Typing.datumKids")]) .full) h
            (dFalse L dHyp) Γ Φ ψ
      linkK K "datumFixed: not a numeral" <|
        decideIn K (fun Γ ↦ pc P "Typing.hasName"
            [nodeT (Term.pair (numeral 0) (cs Γ)), pc P "Typing.envNums" [env Γ]])
          byNumeral byNumeral
    -- context: the abbreviations, the environment, the children, the label, the outermost last
    let lab (Γ : List Tree) : Term := atPos 0 Γ
    let kids (Γ : List Tree) : Term := atPos 1 Γ
    let env (Γ : List Tree) : Term := atPos 2 Γ
    let nums (Γ : List Tree) : Term := atPos 3 Γ
    let body : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
      -- each universal introduction appends truth
      let hAll := 2
      let hNums := Φ₁.length - 3
      let hSrc := Φ₁.length - 2
      let hPd := Φ₁.length - 1
      -- an atom: the erasure the atom; the expansion's characters fixed, by the source forms'
      -- test, and the name's abbreviation decided
      let name (Γ : List Tree) : Term := nodeT (Term.pair (numeral 0) (kids Γ))
      let atomNums : Deducer := linkK K "datumFixed: the atom's expansion" <|
        K.cutThm "charsFixedEq" (fun Γ ↦ [kids Γ, nums Γ]) <| linkK K "datumFixed: cut" <|
        K.impE (linkK K "datumFixed: the characters fixed" (K.byHyp hSrc)) <|
        linkK K "datumFixed: the characters' map" <| fun Γ Φ ψ ↦
        dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta (T.argIdx 3)]) .full) (
        decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [name Γ, nums Γ]])
          (K.solve 3) <|
        linkK K "datumFixed: abbreviated" <|
        dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) hNums <|
        K.allEΓ name <| K.conjE fun Γ Φ ψ ↦
        dImpE L (Φ.length - 1) (K.solve 3) (fun Γ Φ ψ ↦
          decideIn K (fun Γ ↦ pc P "Typing.hasName" [name Γ, pc P "Typing.envNums" [env Γ]])
            refuteAny (splitTests hPd refuteAny) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
      let either (k : Deducer) : Deducer := fun Γ Φ ψ ↦
        (K.solve 3 Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ
      let atom : Deducer :=
        linkK K "datumFixed: atom" <| dConjI L (either atomNums) (either atomNums)
      -- the goal normalized with the erasure's and the expansion's steps unfolded
      let solveSteps : Deducer := fun Γ Φ ψ ↦
        dRwBy (evalRw KL.G KL.E (KL.rules Φ ++ [.delta (T.argIdx 2), .delta (T.argIdx 3)]) .full)
          (KL.solve 3) Γ Φ ψ
      -- a hypothesis renormalized, after a case analysis has split the children
      let renorm (h : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
        dRwHyp (evalRw KL.G KL.E (KL.rulesEx Φ h) .full) h k Γ Φ ψ
      -- the head a numeral's atom, else the test refuted; no keyword the erasure rewrites names it
      let headed (hE hN : ℕ) : Deducer := fun Γ Φ ψ ↦
        KL.listCase treeTy (kids Γ) (splitTests hPd refuteAny) (fun Γ Φ ψ ↦
        KL.treeNode (v 1) (fun Γ₂ Φ₂ ψ₂ ↦
          let cs (Γ' : List Tree) : Term := v (Γ'.length - Γ₂.length)
          let X := ((evalRw KL.G KL.E (KL.rules Φ₂) .full Γ₂ Φ₂ (v 1)).map Prod.fst).getD (v 1)
          dBits L KL.G KL.E (ix "listCases") (ix "bitCases") (fun bs ↦
            match bs.map Oitavem.rank with
            | some 1 => linkK KL "datumFixed: a numeral head" <|
                erasedKeywords.foldr (fun kw k ↦
                  decideBits KL (fun Γ ↦ call D.equal [] [nodeT (Term.pair (numeral 0) (cs Γ)),
                    pc P kw []]) k
                    (linkK KL s!"datumFixed: the keyword {kw}" <|
                    KL.cutThm "equalSound" (fun Γ ↦ [nodeT (Term.pair (numeral 0) (cs Γ))]) <|
                    KL.allEΓ (fun _ ↦ pc P kw []) <| KL.impE (KL.solve 3) fun Γ Φ ψ ↦
                    KL.image (Φ.length - 1) (fun t ↦ apps childrenT [t])
                      (refuteNumeral env cs) Γ Φ ψ))
                  (renorm hE (fun Γ Φ ψ ↦ renorm hN solveSteps Γ Φ ψ))
            | _ => splitTests hPd refuteAny) 2 [] X Γ₂ Φ₂ ψ₂) Γ Φ ψ) Γ Φ ψ
      -- a list: the test's head and children decided, the children fixed, their equations
      -- normalized
      let list : Deducer := linkK K "datumFixed: list" <| splitTests hPd <|
        KL.cutThm "datumAll" (fun Γ ↦ [kids Γ]) <| KL.impE (KL.byHyp hAll) <| KL.allEΓ env <|
        KL.allEΓ nums <| KL.impE (KL.byHyp hNums) <| KL.impE (KL.byHyp hSrc) <|
        KL.impE (linkK KL "datumFixed: the children's test" (KL.solve 3)) <| KL.conjE <|
        fun Γ Φ ψ ↦
        let hE := Φ.length - 2
        let hN := Φ.length - 1
        dRwHyp (evalRw KL.G KL.E (KL.rulesEx Φ hE) .full) hE (fun Γ Φ ψ ↦
        dRwHyp (evalRw KL.G KL.E (KL.rulesEx Φ hN) .full) hN (fun Γ Φ ψ ↦
        dConjI L (linkK KL "datumFixed: the list's erasure" (headed (Φ.length - 2) (Φ.length - 1)))
          (linkK KL "datumFixed: the list's expansion" solveSteps) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
      let X := ((evalRw K.G K.E (K.rules Φ₁) .full Γ₁ Φ₁ (lab Γ₁)).map Prod.fst).getD (lab Γ₁)
      dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
        match bs.map Oitavem.rank with
        | some 1 => atom
        | some 2 => list
        | _ => linkK K "datumFixed: another label" (splitTests hPd refuteAny)) 2 [] X Γ₁ Φ₁ ψ₁
    let node : Deducer :=
      K.cutThm "datumFixedAll" (fun Γ ↦ [kids Γ]) <| K.impE dHyp <|
        dAllI L <| dAllI L <| dImpI L <| dImpI L <| dImpI L body
    let some d := node [list treeTy, bitsTy] [Internal.roseHyp 0 1 φ]
        (Internal.roseNodeAt 2 treeTy bitsTy φ)
      | dbgTrace "datumFixed: not proved" fun _ ↦ none
    pure (⟨0, [treeTy], [], φ⟩, nd (.roseIndHyp 2 0 1) [d]))

/-- The typing's form of a tree, in a typing environment: the first component of the typing's
fold's value at the tree applied to the unit's element. -/
def typedAt (T : Defs3) (env x : Term) : Term :=
  Term.fst (Term.app (Term.snd (T.foldAt 1 [env] x)) Term.star)

/-- The formula that the typing's form of a source form is the form, at the tree of index 0: at
every typing environment and abbreviations, a source form is its own typing's form. -/
def typedφ (P : Prog) (T : Defs3) : Term :=
  -- under the abbreviations v0, the environment v1, the tree v2
  Internal.Logic.all P.o T.envTy (Term.lam T.envTy (Internal.Logic.all P.o (list treeTy)
    (Term.lam (list treeTy) (Internal.Logic.imp P.o (srcAt P (v 0) (v 2))
      (Term.eq (typedAt T (v 1) (v 2)) (v 2))))))

/-- The typing's forms of a list's children ({lit}`typedφ`): where the formula holds at each child
and the list of the children is a source form, the map of the typing's form over the children is
the children; by induction on the list, the head's and the rest's tests decided, false refuted, the
head by its formula, the rest by the induction hypothesis. -/
def typedAll (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("typedAll", fun ix E ↦ do
    let K := datumKit P S ix E
      ((vocab3 ++ ["srcCons"]).filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size)
    let L := K.L
    let o := P.o
    let listOf (xs : Term) : Term := nodeT (Term.pair (numeral 2) xs)
    -- under the abbreviations v0, the environment v1, the list v2
    let ψ := Internal.Logic.imp o (S.allL (Term.lam treeTy (typedφ P T)) (v 0))
      (Internal.Logic.all o T.envTy (Term.lam T.envTy (Internal.Logic.all o (list treeTy)
        (Term.lam (list treeTy) (Internal.Logic.imp o (srcAt P (v 0) (listOf (v 2)))
          (Term.eq (mapT (fun c ↦ typedAt T (v 3) c) (v 2)) (v 2)))))))
    let some d₀ := dImpI L (dAllI L (dAllI L (dImpI L (linkK K "typedAll: nil" (K.solve 3)))))
        [] [] (Term.subst ψ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "typedAll: nil" fun _ ↦ none
    -- a construction: hypotheses the induction hypothesis, the construction's formulas, the
    -- source forms' test; the head's test and the rest's decided, false refuted
    let cons : Deducer := dImpI L (dAllI L (dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      -- each universal introduction appends truth
      let hAll := Φ₁.length - 4
      let hSrc := Φ₁.length - 1
      let nums (Γ : List Tree) : Term := v (Γ.length - Γ₁.length)
      let env (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + 1)
      let tail (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + 2)
      let head (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + 3)
      let src (Γ : List Tree) (x : Term) : Term := pc P "srcForm"
        [Term.lam treeTy (pc P "Reader.expandNums" [Term.rename (nums Γ) (· + 1), v 0]), x]
      let refute : Deducer := linkK K "typedAll: refute" fun Γ Φ ψ ↦ K.hypFalse hSrc Γ Φ ψ
      (linkK K "typedAll: cons" <|
      decideIn K (fun Γ ↦ src Γ (head Γ)) refute <|
      decideIn K (fun Γ ↦ src Γ (listOf (tail Γ))) refute <|
      -- the head by its formula; the rest's map by the induction hypothesis
      linkK K "typedAll: decided" fun Γ₂ Φ₂ ψ₂ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₂ hAll) .full) hAll (linkK K "typedAll: split" <|
      K.conjE fun Γ Φ ψ ↦
        let hHead := Φ.length - 2
        let hRest := Φ.length - 1
        dAllE L K.G K.E hHead (env Γ) (K.allEΓ nums
          (K.impE (linkK K "typedAll: head's source" (K.solve 3)) fun Γ Φ ψ ↦
          dImpE L 0 (K.byHyp hRest) (K.allEΓ env (K.allEΓ nums
            (K.impE (linkK K "typedAll: rest's source" (K.solve 3))
              (linkK K "typedAll: maps" (K.solve 3))))) Γ Φ ψ)) Γ Φ ψ) Γ₂ Φ₂ ψ₂)
        Γ₁ Φ₁ ψ₁)))
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem ψ] (Internal.listConsAt 1 treeTy ψ)
    pure (⟨0, [list treeTy], [], ψ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The typing's form of a node of a label of {name}`listLabels`, the node of the children's
forms, in the context of the children and the typing environment: the children of the form's
normal form by the datatype language's vocabulary and the typing's form of a node of the label
({lit}`rawRule`), the map of the typing's form over the children, by induction on the children. -/
def typedNode (P : Prog) (S : Defs) (T : Defs3) (label : ℕ) (rawRule : String) : Step :=
  (s!"typedNode{label}", fun ix E ↦ do
    let K := datumKit P S ix E ((vocab3 ++ [rawRule]).filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size)
    let nodeOf (xs : Term) : Term := nodeT (Term.pair (numeral label) xs)
    let Γ := [list treeTy, T.envTy]
    let rs := K.rules []
    -- the children of a node's normal form, a node's being a pair of the label and the children
    let kidsOf (t : Term) : Option Term := match t.label, t.children with
      | .arr 2 _, [p] => match p.label, p.children with
        | .pair, [_, xs] => some xs
        | _, _ => none
      | _, _ => none
    let some l := (nfE K.G E rs Γ (typedAt T (v 1) (nodeOf (v 0)))).bind kidsOf
      | dbgTrace s!"typedNode{label}: left" fun _ ↦ none
    let some r := nfE K.G E rs Γ (mapT (fun c ↦ typedAt T (v 3) c) (v 0))
      | dbgTrace s!"typedNode{label}: right" fun _ ↦ none
    let some d := Internal.byListIndHyp K.G E 0 0 1 rs 4096 Γ [] l r
      | dbgTrace s!"typedNode{label}: {showT l}\n  = {showT r}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The typing's forms at the labels of {name}`listLabels`: the raw forms at the checked nodes
({name}`rawAt`), the children's forms at each label ({name}`typedNode`), and the source forms'
test at the checked nodes, the list's ({name}`srcChecked`). -/
def typedNodes (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [rawAt P T "rawCase" 13 [], rawAt P T "rawCata" 14 [], typedNode P S T 2 "rawList",
    typedNode P S T 13 "rawCase", typedNode P S T 14 "rawCata", srcChecked P S T 13,
    srcChecked P S T 14]

/-- The typing's form of a source form is the form ({lit}`typedφ`), by induction on rose trees,
the hypothesis of induction the formula at every child: the node's label decided. At an atom the
typing's form is the atom ({name}`rawAtom`); at a list, or a checked node, whose source forms' test
is the list's, the node of the children's forms ({name}`rawList`, {name}`rawAt`,
{name}`typedNode`), the children by {name}`typedAll`; at a node of another label the source forms'
test is false. -/
def typedFixed (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("typedFixed", fun ix E ↦ do
    let more := (vocab3 ++ ["rawAtom", "rawList", "rawCase", "rawCata", "typedNode2",
      "typedNode13", "typedNode14", "srcChecked13", "srcChecked14"]).filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size
    let K := datumKit P S ix E more
    let L := K.L
    let φ := typedφ P T
    -- context: the abbreviations, the environment, the children, the label, the outermost last
    let lab (Γ : List Tree) : Term := atPos 0 Γ
    let kids (Γ : List Tree) : Term := atPos 1 Γ
    let env (Γ : List Tree) : Term := atPos 2 Γ
    let nums (Γ : List Tree) : Term := atPos 3 Γ
    let body : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
      let hAll := 2
      let hSrc := Φ₁.length - 1
      let atom : Deducer := linkK K "typedFixed: atom" (K.solve 3)
      -- a list, or a checked node, whose source forms' test is the list's
      let list : Deducer := linkK K "typedFixed: list" <|
        K.cutThm "typedAll" (fun Γ ↦ [kids Γ]) <| K.impE (K.byHyp hAll) <| K.allEΓ env <|
        K.allEΓ nums <| K.impE (K.byHyp hSrc) <| linkK K "typedFixed: the list's form" (K.solve 3)
      let other : Deducer := linkK K "typedFixed: another label" fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ hSrc ++ [.delta (T.argIdx 5)]) .full) hSrc
          (dFalse L dHyp) Γ Φ ψ
      let X := ((evalRw K.G K.E (K.rules Φ₁) .full Γ₁ Φ₁ (lab Γ₁)).map Prod.fst).getD (lab Γ₁)
      dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
        match bs.map Oitavem.rank with
        | some 1 => atom
        | some 2 | some 13 | some 14 => list
        | _ => other) 4 [] X Γ₁ Φ₁ ψ₁
    let node : Deducer :=
      K.cutThm "typedFixedAll" (fun Γ ↦ [kids Γ]) <| K.impE dHyp <|
        dAllI L <| dAllI L <| dImpI L body
    let some d := node [list treeTy, bitsTy] [Internal.roseHyp 0 1 φ]
        (Internal.roseNodeAt 2 treeTy bitsTy φ)
      | dbgTrace "typedFixed: not proved" fun _ ↦ none
    pure (⟨0, [treeTy], [], φ⟩, nd (.roseIndHyp 2 0 1) [d]))

/-- The relation's fold, its value type and step, from its definition. -/
def relFold (P : Prog) (T : Defs3) : Option (Tree × Term) := do
  let some (.language d) := P.G.defs[T.q]? | none
  let (C, st, _, _) ← firstFold d.body
  pure (C, st)

/-- The rebuilding of a type's tree by the relation's fold, whose value at a node pairs the node
rebuilt from the children's first components with the relation there: at the children, where
the first component at each child is the child, the children rebuilt are the children, by
induction on the children; and the first component at every tree is the tree, by induction on
rose trees. -/
def relRebuild (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  match relFold P T with
  | none => []
  | some (C, st) =>
    let fstAt (x : Term) : Term := Term.fst (Term.roseRec C st x)
    let φ : Term := Term.eq (fstAt (v 0)) (v 0)
    let kids (xs : Term) : Term := Term.listRec (nilT treeTy) (consT treeTy (Term.fst (v 1)) (v 0))
      (Term.listRec (nilT C) (consT C (Term.roseRec C st (v 1)) (v 0)) xs)
    [("relKids", fun ix E ↦ do
        let K : Kit := ⟨P, S, E, ix, []⟩
        let L := K.L
        let ψ := Internal.Logic.imp P.o (S.allL (Term.lam treeTy φ) (v 0))
          (Term.eq (kids (v 0)) (v 0))
        let d₀ ← dImpI L (K.solve 2) [] [] (Term.subst ψ (Internal.instVar
          (Term.arr 0 [treeTy] Term.star)))
        -- a construction: the head's by its hypothesis, the rest's by the induction hypothesis
        let cons : Deducer := dImpI L fun Γ Φ ψ ↦
          let hA := Φ.length - 1
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ hA) .full) hA (K.conjE fun Γ Φ ψ ↦
            dImpE L 0 (K.byHyp (Φ.length - 1)) (K.solve 3) Γ Φ ψ) Γ Φ ψ
        let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem ψ]
          (Internal.listConsAt 1 treeTy ψ)
        pure (⟨0, [list treeTy], [], ψ⟩, nd (.listIndHyp 0 1) [d₀, d₁])),
      -- the map of the first components over the map of the fold, the map of the first
      -- component at each child, by induction on the children
      ("relFus", fun ix E ↦ do
        let rs := vRules P ix
        let Γ := [list treeTy]
        let r := Term.listRec (nilT treeTy) (consT treeTy (fstAt (v 1)) (v 0)) (v 0)
        let some l' := nfE P.G E rs Γ (kids (v 0)) | dbgTrace "relFus: left" fun _ ↦ none
        let some r' := nfE P.G E rs Γ r | dbgTrace "relFus: right" fun _ ↦ none
        let some d := Internal.byListIndHyp P.G E 0 0 1 rs 4096 Γ [] l' r'
          | dbgTrace "relFus: not proved" fun _ ↦ none
        pure (⟨0, Γ, [], Term.eq l' r'⟩, d)),
      -- the first component and the identity both satisfy the fold's equation of rebuilding
      ("relFst", fun ix E ↦ do
        let rs := [.thm (ix "relFus") []] ++ vRules P ix
        let some d := byRoseIndWith P.G 0 (nodeT (Term.pair (v 1) (v 0)))
            (byMode .full P.G E 0 rs) [treeTy] [] (fstAt (v 0)) (v 0)
          | let s := nodeT (Term.pair (v 1) (v 0))
            let show2 (t : Term) : String := match Internal.roseParts treeTy,
                Internal.typeIn P.G 0 [treeTy] t with
              | some (a, _), some Ct =>
                let l := Internal.roseNodeAt 2 treeTy a t
                let r := Term.subst s (Internal.atVar0 (Internal.roseMapAt 0 1 Ct t))
                let n (x : Term) := ((nfE P.G E rs [list treeTy, a] x).map showT).getD "none"
                s!"{n l}\n    = {n r}"
              | _, _ => "no parts"
            dbgTrace s!"relFst: not proved:\n  {show2 (fstAt (v 0))}\n  {show2 (v 0)}"
              fun _ ↦ none
        pure (⟨0, [treeTy], [], φ⟩, d))]

/-- The names of the rebuilding lemmas of the relation's fold. -/
def relRebuildNames : List String := ["relFst"]

/-- The arguments of the first equality of trees in a term. -/
def equalArgs : Term → Option (Term × Term) := RoseTree.para fun l cs ↦
  match l, cs.map Prod.fst with
  | .defn k _, [x, y] => if k = D.equal then some (x, y) else cs.findSome? (·.2)
  | _, _ => cs.findSome? (·.2)

/-- A member's quotation related at the datatype a form names: where the relation's markers are
the typing environment's, the type {lit}`y` a datatype the environment declares and the form
{lit}`D` names by its own name ({lit}`Typing.namesData`), and the tree a member of the datatype
{lit}`D` names, the tree's quotation is related at {lit}`y`. In the context of the tree, the form,
the type, the environment and the relation's context. -/
def relTDatumThm (P : Prog) (T : Defs3) : Internal.Thm :=
  ⟨0, [treeTy, treeTy, treeTy, T.envTy, Defs3.ctxTy],
    [Term.eq (Term.snd (v 4)) (pc P "Typing.envMs" [v 3]),
      truth P.o (pc P "Typing.namesData" [v 3, v 2, v 1]),
      truth P.o (pc P "Typing.memberOf" [pc P "Typing.envMs" [v 3], v 1, v 0])],
    Term.app (T.relT (v 4) (v 2)) (pc P "Eval.valQuote" [v 0])⟩

/-- A member's quotation related at the datatype a form names ({name}`relTDatumThm`): the type a
node, its label decided by the test of its naming, at the label of datatypes the relation
unfolded, the tree its witness; the form an atom, its label decided, and the name's equality with
the atom's characters, by the equality's soundness, makes the relation's atom the form. -/
def relTDatum (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relTDatum", fun ix E ↦ do
    let K := datumKit P S ix E ((vocab3 ++ ["relTTree"] ++ relRebuildNames).filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size)
    let L := K.L
    let a := relTDatumThm P T
    let childrenT ← primT Kernel.Prim.children
    let namesD := Internal.NormRule.delta (P.idx "Typing.namesData")
    -- the tree a member, the relation's markers rewritten to the environment's
    let member : Deducer := dRwBy (evalRw K.G K.E [.hyp 0] .full) (K.byHyp 2)
    -- the test of the type's naming with its tests decided, false refuted
    let tests (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 1 ++ [namesD]) .full) 1
        (K.splitHyp (Φ.length) (fun Γ Φ ψ ↦ (anyFalse K Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ) 16)
        Γ Φ ψ
    -- the type a node, its label decided by the test of its naming; the name's equality with the
    -- form's name, which the test compares, by its soundness, the image of its children cut in;
    -- the relation unfolded, the tree its witness
    let some d := (linkK K "relTDatum" <| K.treeNode (atPos 2 a.ctx) <| fun Γ Φ ψ ↦
        let body : Deducer := fun Γ Φ ψ ↦ (K.treeNode (atPos 3 Γ) <| tests <|
          linkK K "relTDatum: a datatype" <| fun Γ Φ ψ ↦ do
          let some (x, y) := (List.range Φ.length).reverse.findSome? fun h ↦ do
              let t ← Φ[h]?
              let (n, _) ← evalRw K.G K.E (K.rulesEx Φ h) .full Γ Φ t
              equalArgs n
            | traceK K "relTDatum: no equality" Γ Φ ψ
          let attempt (x y : Term) : Deducer :=
            K.cutThm "equalSound" (fun _ ↦ [x]) <| K.allEΓ (fun _ ↦ y) <|
            K.impE (K.solve 3) <| fun Γ Φ ψ ↦
            -- the goal normalized without the name's equation, so that the relation's rebuilding
            -- of the name is the name before the name is rewritten
            let hEq := Φ.length - 1
            K.image hEq (fun t ↦ apps childrenT [t]) (fun Γ Φ ψ ↦
              dRwBy (evalRw K.G K.E (K.rulesEx Φ hEq ++ [.delta T.q]) .full)
                (linkK K "relTDatum: the witness" <|
                  dExI L K.G K.E (atPos 4 Γ) (dConjI L (K.solve 3) member)) Γ Φ ψ) Γ Φ ψ
          (attempt x y Γ Φ ψ).orElse fun _ ↦ attempt y x Γ Φ ψ) Γ Φ ψ
        -- no children: the name the default, the form's characters none
        let none' : Deducer := fun Γ Φ ψ ↦ (K.treeNode (atPos 3 Γ) <| tests <|
          linkK K "relTDatum: no children" <| fun Γ Φ ψ ↦
          K.listCase treeTy (atPos 8 Γ) (fun Γ Φ ψ ↦ dRwBy (evalRw K.G K.E
              (K.rules Φ ++ [.delta T.q]) .full) (dExI L K.G K.E (atPos 4 Γ)
              (dConjI L (K.solve 3) member)) Γ Φ ψ)
            (anyFalse K) Γ Φ ψ) Γ Φ ψ
        -- the type's children split, so that the relation reads the first
        K.listCase treeTy (atPos 6 Γ) none' body Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "relTDatum: not proved" fun _ ↦ none
    pure (a, d))

/-- The lemmas of the soundness at datums. -/
def datumLemmas (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  datumVocab P T ++ datumEqs P S T ++ [mapFixed P S, srcCons P S T, datumAll P S T] ++
    stageValues P S T ++
    [roseAllFor P S "datumFixedAll" (datumφ P T), datumFixed P S T] ++ relRebuild P S T ++
    [relTDatum P S T]

/-- The soundness at a datum, at source forms: the keyword of quotation, which the erasure writes,
no numeral abbreviation; the elements' expansions present and source forms; the typing's reading of
the type and of the datum present, each absent refuting the typing, and the tests of the typing's
rule decided, false refuting it: the datatype the form names, decided before the datum's reading as
the typing's conjunction reads it, the datum a datum as the reader reads it
({lit}`Typing.plainDatum`) and a member; the erasure and the expansion of numeral abbreviations
fixing the datum ({name}`datumFixed`), so that the reader reads the datum the typing read, present;
the value, at the first level, the datum's quotation, related at the datatype ({name}`relTDatum`).
-/
def datumCase (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("datumCase", fun ix E ↦ do
    let kw := "Typing.kwDatum"
    -- the typing's tests and the reader's reading of a datum kept folded, the decisions reading
    -- them whole
    let W₀ := kwKit P S T ix E 2 [false, false] kw
    let W : KwKit := { W₀ with K := { W₀.K with
      P := { W₀.K.P with folded := W₀.K.P.folded ++ datumCaseTests } } }
    let K := W.K
    let L := K.L
    let a := kwThm P S T kw 2 [false, false]
    -- under the statement's quantifiers, the element's form v nQ: its expansion x, the typing's
    -- form of it, the type's form with its abbreviations expanded
    let x := pc P "Prelude.get" [pc P "Datatype.expandExpr" [v 7, v nQ]]
    let typed (t : Term) : Term := Term.fst (Term.app (Term.snd (T.foldAt 1 [v 6] t)) Term.star)
    let tyForm := pc P "Datatype.expandAliases" [v 7, x]
    let readTy := pc P "Typing.readTy" [v 6, typed tyForm]
    let typedDatum := pc P "Reader.readDatum" [typed x]
    let at_ (c : ℕ) (t : Term) (Γ : List Tree) : Term := W.inΓ (atPos c) Γ t
    -- a value read, in normal form: the variable its generalization introduced
    let readOf (c : ℕ) (t : Term) (Γ : List Tree) (Φ : List Term) : Term :=
      ((evalRw K.G K.E (K.rules Φ) .full Γ Φ (pc P "Prelude.get" [at_ c t Γ])).map
        Prod.fst).getD Term.star
    -- a test of the typing's rule decided, false refuting the typing; the test's terms read in the
    -- hypotheses at hand
    let test (msg : String) (t : List Tree → List Term → Term) (k : Deducer) : Deducer :=
      fun Γ Φ ψ ↦ decideIn K (fun Γ' ↦ t Γ' Φ) (verifyK K s!"datum: {msg} refuted"
        (linkK K s!"datum: {msg} refuted" (W.hypFalseU (W.hyp 6)))) k Γ Φ ψ
    let eval : Deducer := fun Γ Φ ψ ↦
      let X := evalTools K Φ [] []
      let r := readOf 1 typedDatum Γ Φ
      let y := readOf 0 readTy Γ Φ
      let w := pc P "Eval.valQuote" [r]
      X.norm (dConv L K.G K.E S (succN zeroN) w
        (verifyK K "datum stable" <| linkK K "datum stable" X.byNorm)
        (verifyK K "datum related" <| linkK K "datum related" <|
          W.cutApply "relTDatum" (fun Γ ↦ [r, at_ 0 (typed tyForm) Γ, y, W.qv 4 Γ, W.qv 10 Γ])
            [W.byStmt 10, linkK K "datum: the naming" (K.solve 3),
              linkK K "datum: the membership" (K.solve 3)] <|
          linkK K "datum: the relation" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ
    -- the erasure and the expansion of numeral abbreviations fixing the datum's expansion
    let fixed (k : Deducer) : Deducer :=
      linkK K "datum: fixed" <| K.cutThm "datumFixed" (fun Γ ↦ [at_ 1 x Γ]) <|
        K.allEΓ (W.qv 4) <| K.allEΓ (W.qv 7) <| K.impE (W.byStmt 2) <|
        K.impE (linkK K "datum: the source form" (K.solve 3)) <|
        K.impE (linkK K "datum: the datum's form" (K.solve 3)) <| K.conjE <|
        fun Γ Φ ψ ↦
        let hE := Φ.length - 2
        let hN := Φ.length - 1
        -- the equations' stage functions unfolded as the hypotheses' are, so that their left
        -- sides meet the resolved term's
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ hE) .full) hE (fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ hN) .full) hN (fun Γ Φ ψ ↦
            unfoldApps K W.ks [Φ.length - 2, Φ.length - 1] k 6 true false Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let naming : Deducer → Deducer :=
      test "the datatype's naming" (fun Γ Φ ↦ pc P "Typing.namesData"
          [W.qv 4 Γ, readOf 0 readTy Γ Φ, at_ 0 (typed tyForm) Γ])
    let tests : Deducer :=
      test "the datum's form" (fun Γ _ ↦
        pc P "Typing.plainDatum" [W.qv 4 Γ, at_ 1 (typed x) Γ]) <|
      test "the membership" (fun Γ Φ ↦ pc P "Typing.memberOf" [pc P "Typing.envMs" [W.qv 4 Γ],
          at_ 0 (typed tyForm) Γ, readOf 1 typedDatum Γ Φ]) <|
      fixed <| K.norm eval
    -- the type's form a source form as the form's expansion holds it, its abbreviations expanded
    let srcTest (c : ℕ) : Term := if c = 0 then
        pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [v 4, v 0]), tyForm]
      else W.sourceTest
    let pres (c : ℕ) (msg : String) (t : Term) (i : ℕ) (u : Bool) (k : Deducer) : Deducer :=
      W.present msg (fun Γ ↦ W.inΓ (atPos c) Γ t) i k u
    let chain : Deducer :=
      -- the quotation's keyword, which the erasure writes, not abbreviated
      W.plainKw "Reader.kwQuote" (Kit.solve { K with more := K.more ++ lookupEqNames } 3) <|
      pres 0 "expansion 0" (pc P "Datatype.expandExpr" [v 7, v nQ]) 5 true <|
      pres 1 "expansion 1" (pc P "Datatype.expandExpr" [v 7, v nQ]) 5 true <|
      (W.sources · srcTest) <| W.unfold <|
      pres 0 "readTy" readTy 6 false <|
      -- the typing's form of the datum the datum, a source form
      K.cutThm "typedFixed" (fun Γ ↦ [at_ 1 x Γ]) <| K.allEΓ (W.qv 4) <| K.allEΓ (W.qv 7) <|
      K.impE (linkK K "datum: the typing's form" (K.solve 3)) <| normLastK K <|
      -- the datatype's naming decided first, the typing's conjunction reading it before the
      -- datum's presence; then the datum read, its presence a single test
      K.norm <| naming <|
      (fun k ↦ decideIn K (fun Γ ↦ pc P "Prelude.isSome" [at_ 1 (pc P "Reader.readDatum" [x]) Γ])
        (fun Γ Φ ψ ↦
          let h := W.hyp 6
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h (dFalse L dHyp) Γ Φ ψ)
        (W.generalize (fun Γ ↦ pc P "Prelude.get" [at_ 1 (pc P "Reader.readDatum" [x]) Γ]) k)) <|
      K.norm tests
    -- the statement's hypotheses introduced; the keyword's being a numeral abbreviation is
    -- immaterial, the erasure dropping it before the abbreviations are expanded
    let some d := (List.range nQ).foldr (fun _ k ↦ dAllI L k)
        ((List.range W.nH).foldr (fun _ k ↦ dImpI L k) (verifyK K "datum" chain))
        a.ctx a.hyps a.concl
      | dbgTrace s!"{kw}: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness at datums: the lemmas and the stage functions' equations at a
datum, the tests of {name}`datumCaseTests` folded. -/
def datumDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  datumLemmas P S T ++ typedNodes P S T ++
    [typedAll P S T, roseAllFor P S "typedFixedAll" (typedφ P T), typedFixed P S T] ++
    kwEqs { P with folded := P.folded ++ datumCaseTests } T "Typing.kwDatum" 2

/-- The soundness at a datum after the base's, the atom's, the list's and the datum's
declarations. -/
def datumCaseCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (datumDev3 P S T).map (·.1)) "datum-case" [datumCase P S T] before

/-- The development of the soundness at datums ({name}`datumDev3`), after the base's, the atom's
and the list's declarations, stored as the certificate {lit}`datatype-datum`. -/
def datumCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P names "datatype-datum" (datumDev3 P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
