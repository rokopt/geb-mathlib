/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeCataChain
public meta import GebTests.Prototypes.FreeTopos.DatatypeCataChain -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at a structural recursion

The soundness of the datatype language's stage-1 compiler at a structural recursion: the kernel's
fold of trees whose step sees the node, at a step whose value at a node is a suspended result,
converges at every tree, to a suspended result related at its type at a tree that is a member of
the datatype.

## Main definitions

* {lit}`cataSoundCertificates` — the development, stored as the certificate
  {lit}`datatype-cata-sound`.

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

/-- A suspended result of a tree related: where the tree's memberships pass the test of a field of
the datatype {lit}`d`, the value {lit}`w` is related, in the relation's context {lit}`D`, at the
type of a suspended result of the result type {lit}`R`. -/
def thunkRel (P : Prog) (T : Defs3) (E d D R t w : Term) : Term :=
  let ms := pc P "Typing.envMs" [E]
  Internal.Logic.imp P.o
    (truth P.o (pc P "Typing.fieldOk" [ms, d, pc P "Typing.memberships" [ms, t]]))
    (Term.app (T.relT D (thunkTy P R)) w)

/-- The suspended results' relation ({name}`relatedT`) at the rests and a result of the child
related ({name}`thunkRel`) gives it at the constructions: at an index, either the first, the result
related, or a successor, the rests' ({lit}`nthSuccRaw`). In the context of the rest of the results,
the result, the rest of the children, the child, the result type, the relation's context, the
datatype and the typing environment. -/
def relatedCons (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relatedCons", fun ix E ↦ do
    let K : Kit := ⟨walkProg P, S, E, ix, []⟩
    let L := K.L
    let Γ := [list treeTy, treeTy, list treeTy, treeTy, treeTy, Defs3.ctxTy, treeTy, T.envTy]
    let rel (ts rs : Term) : Term := relatedT P T (v 7) (v 6) (v 5) (v 4) ts rs
    let a : Internal.Thm := ⟨0, Γ, [Internal.Logic.tt P.o,
      thunkRel P T (v 7) (v 6) (v 5) (v 4) (v 3) (v 1), rel (v 2) (v 0)],
      rel (consT treeTy (v 3) (v 2)) (consT treeTy (v 1) (v 0))⟩
    let (rs, r, ts, t) := (atPos 7, atPos 6, atPos 5, atPos 4)
    let some (Internal.Entry.language bs) := E[ix "bitsSucc"]? | none
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let succAt (p : List Tree → Term) (xs x : List Tree → Term) (k : Deducer) : Deducer :=
      K.cutThm "nthSuccRaw" (fun Γ ↦ [p Γ, xs Γ, x Γ]) (normLastK K k)
    let some d := (dAllI L <| dImpI L fun Γ₀ Φ₀ ψ₀ ↦
        let iMem := Φ₀.length - 1
        let i := v 0
        -- the first: its member's test the child's, the result related
        let head : Deducer := linkK K "relatedCons: the first" fun Γ Φ ψ ↦
          dImpE L 1 (linkK K "relatedCons: the member" (K.byHyp iMem))
            (K.norm (dConjI L (K.solve 3) byLast)) Γ Φ ψ
        -- a successor: the rests' at the predecessor
        let succ : Deducer := linkK K "relatedCons: a successor" <| K.exE fun Γ Φ ψ ↦
          let p := atPos (Γ.length - 1)
          (succAt p ts t <| succAt p rs r <|
            dAllE L K.G K.E 2 (p Γ) <|
            K.impE (linkK K "relatedCons: the rest's member" (K.byHyp iMem)) <|
            linkK K "relatedCons: the rest's result" byLast) Γ Φ ψ
        dCut (Internal.instTerm [] [i] bs.concl) (nd (.apply (ix "bitsSucc") [] [i]))
          (dDisjE L Φ₀.length head succ) Γ₀ Φ₀ ψ₀)
        a.ctx a.hyps a.concl
      | dbgTrace "relatedCons: not proved" fun _ ↦ none
    pure (a, d))

/-- A function's values at each child converging, each suspended result of its child related
({name}`thunkRel`), the values collected ({lit}`Eval.allSomeT`) converge to a node of values as many
as the children and related to them ({name}`relatedT`): by induction on the children, as
{lit}`allConv`, a construction's relation by {name}`relatedCons`. In the context of the children,
the function, the result type, the relation's context, the datatype and the typing environment. -/
def relatedConv (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relatedConv", fun ix E ↦ do
    let K : Kit := ⟨walkProg P, S, E, ix, lenRules.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let L := K.L
    let FTy := exp nat (exp treeTy treeTy)
    let Γ := [list treeTy, FTy, treeTy, Defs3.ctxTy, treeTy, T.envTy]
    let hyp : Term := S.allL (Term.lam treeTy (S.conv (Term.lam nat (apps (v 3) [v 0, v 1]))
      (Term.lam treeTy (thunkRel P T (v 7) (v 6) (v 5) (v 4) (v 1) (v 0))))) (v 0)
    let concl : Term := S.conv
      (Term.lam nat (pc P "Eval.allSomeT" [pc P "Eval.mapT" [Term.app (v 2) (v 0), v 1]]))
      (Term.lam treeTy (Internal.Logic.conj P.o (lenEqT P (v 1) (call D.children [] [v 0]))
        (relatedT P T (v 6) (v 5) (v 4) (v 3) (v 1) (call D.children [] [v 0]))))
    let φ := Internal.Logic.imp P.o hyp concl
    let negated : Deducer := dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let lenOk : Deducer := K.norm <| dConjI L negated negated
    -- the empty list: the empty node at once, no index a member
    let d₀ ← dImpI L (K.conv (fun _ ↦ zeroN) (fun _ ↦ node0 (nilT treeTy))
        (linkK K "relatedConv: empty stable" K.byNorm)
        (linkK K "relatedConv: empty related" <| K.norm <| dConjI L lenOk <|
          dAllI L <| dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ))
      Γ.tail [] (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a construction: positions, the typing environment 0, the datatype 1, the relation's context
    -- 2, the result type 3, the function 4, the head 5 and the rest 6
    let (Ee, dt, Dv, Rty, hd, tl) := (atPos 0, atPos 1, atPos 2, atPos 3, atPos 5, atPos 6)
    let cons : Deducer := dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let fin (n₁ w₁ n₂ w₂ : List Tree → Term) (r₁ r₂ : ℕ) : Deducer := fun Γ Φ ψ ↦
        let (a₁, a₂) := (Φ.length - 2, Φ.length - 1)
        K.conv (fun Γ ↦ S.add (n₁ Γ) (n₂ Γ))
          (fun Γ ↦ node0 (consT treeTy (w₁ Γ) (call D.children [] [w₂ Γ])))
          (linkK K "relatedConv: stable" <|
            K.instN a₁ (fun _ ↦ v 0) (K.instN a₂ (fun _ ↦ v 0) K.byNorm))
          (linkK K "relatedConv: related" fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ r₂) .full) r₂ (K.conjE fun Γ Φ ψ ↦
              let (iLen, iRel) := (Φ.length - 2, Φ.length - 1)
              K.norm (dConjI L
                (linkK K "relatedConv: the lengths" (K.byHyp iLen))
                (linkK K "relatedConv: the results" <|
                  applyThm K "relatedCons" (fun Γ ↦ [call D.children [] [w₂ Γ], w₁ Γ, tl Γ, hd Γ,
                    Rty Γ, Dv Γ, dt Γ, Ee Γ])
                    [K.solve 3, K.byHyp r₁, K.byHyp iRel]
                    fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
      let rest (Γ₃ : List Tree) (s₁ r₁ hr : ℕ) : Deducer :=
        let n₁ (Γ : List Tree) : Term := v (Γ.length - Γ₃.length + 1)
        let w₁ (Γ : List Tree) : Term := v (Γ.length - Γ₃.length)
        let after : Deducer := fun Γ₄ Φ₄ ψ₄ ↦
          let n₂ (Γ : List Tree) : Term := v (Γ.length - Γ₄.length + 1)
          let w₂ (Γ : List Tree) : Term := v (Γ.length - Γ₄.length)
          let (s₂, r₂) := (Φ₄.length - 2, Φ₄.length - 1)
          K.shift s₁ false n₂ (K.shift s₂ true n₁ (fin n₁ w₁ n₂ w₂ r₁ r₂)) Γ₄ Φ₄ ψ₄
        dImpE L 0 (K.byHyp hr) (K.unfoldConv (K.exE (K.exE (K.conjE after))))
      let head (hc hr : ℕ) : Deducer :=
        dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) hc (K.exE (K.exE (K.conjE
          fun Γ₃ Φ₃ ψ₃ ↦ rest Γ₃ (Φ₃.length - 2) (Φ₃.length - 1) hr Γ₃ Φ₃ ψ₃)))
      dRwHyp (evalRw K.G K.E (K.rules Φ₁) .full) (Φ₁.length - 1) (K.conjE fun Γ₂ Φ₂ ψ₂ ↦
        head (Φ₂.length - 2) (Φ₂.length - 1) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "relatedConv: a construction" cons (list treeTy :: treeTy :: Γ.tail)
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The hypothesis of the fold whose step sees the node at the step {lit}`f`, the carried type
{lit}`A`, the result type {lit}`R`, the relation's context {lit}`D`, the datatype {lit}`d` and the
typing environment {lit}`E`: at every tree and results, the step's application to the tree's
quotation and to the results' list value converges to a value which, the results as many as the
tree's children and related to them ({name}`relatedT`), is a suspended result of the tree related
({name}`thunkRel`). -/
def paraStepH (P : Prog) (S : Defs) (T : Defs3) (f A R Dc d E : Term) : Term :=
  let ap (Dv n : Term) : Term := Term.snd (S.levelN (Term.fst Dv) n)
  let imp := Internal.Logic.imp P.o
  let all (B : Tree) (t : Term) : Term := Internal.Logic.all P.o B (Term.lam B t)
  -- beneath the two quantifiers and the level: the level v0, the results v1 and the tree v2
  let stepVal : Term := pc P "Eval.bindO" [apps (ap (sh 3 Dc) (v 0)) [sh 3 f,
      pc P "Eval.valQuote" [v 2]],
    Term.lam treeTy (apps (ap (sh 4 Dc) (v 1)) [v 0, pc P "Eval.ofList" [sh 4 A, v 2]])]
  let ts := call D.children [] [v 2]
  all treeTy <| all (list treeTy) <|
    S.conv (Term.lam nat stepVal) (Term.lam treeTy
      (imp (lenEqT P ts (v 1)) (imp (relatedT P T (sh 3 E) (sh 3 d) (sh 3 Dc) (sh 3 R) ts (v 1))
        (thunkRel P T (sh 3 E) (sh 3 d) (sh 3 Dc) (sh 3 R) (v 2) (v 0)))))

/-- The statement of the fold whose step sees the node, at a tree, the variable of index 0, where
the step's value at a node is a suspended result: for all steps, the types the fold carries, result
types, relation's contexts, datatypes and typing environments, where at every tree and results the
step's application to the tree's quotation and to the results' list value converges to a value
which, the results as many as the tree's children and related to them ({name}`relatedT`), is a
suspended result of the tree related ({name}`thunkRel`), the fold's value at the tree converges to
such a value. -/
def cataParaφ (P : Prog) (S : Defs) (T : Defs3) : Term :=
  let imp := Internal.Logic.imp P.o
  let ap (D n : Term) : Term := Term.snd (S.levelN (Term.fst D) n)
  foralls P.o [treeTy, treeTy, treeTy, Defs3.ctxTy, treeTy, T.envTy] <|
    imp (paraStepH P S T (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) <|
    S.conv (Term.lam nat (pc P "Eval.paraVal" [ap (v 4) (v 0), v 2, v 1, v 7]))
      (Term.lam treeTy (thunkRel P T (v 6) (v 5) (v 4) (v 3) (v 7) (v 0)))

/-- The fold whose step sees the node converges at every tree ({name}`cataParaφ`): by induction on
trees, as {lit}`paraConv`, the children's values converging together by {name}`relatedConv` to
values related to them, and the step's application at those values by the hypothesis, whose
suspended result is then related at the tree. -/
def cataPara (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cataPara", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, ["paraConvFus", "pvFst", "pvKids"]⟩
    let L := K.L
    let φ := cataParaφ P S T
    let pv : List Term → Term := pc P "Eval.paraVal"
    let ap (D n : Term) : Term := Term.snd (S.levelN (Term.fst D) n)
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let body (Γ₁ : List Tree) (hAll hf : ℕ) : Deducer :=
      let at₁ (k : ℕ) (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + k)
      let (f, A, Rt, Dv, dt, Ee, cs, l) := (at₁ 0, at₁ 1, at₁ 2, at₁ 3, at₁ 4, at₁ 5, at₁ 6, at₁ 7)
      let tree (Γ : List Tree) : Term := nodeT (Term.pair (l Γ) (cs Γ))
      let inst : List (List Tree → Term) := [Ee, dt, Dv, Rt, A, f]
      -- the children's convergences at the step, and the function of the level and the child
      let Q (Γ : List Tree) : Term := Term.lam treeTy (S.conv
        (Term.lam nat (pv [ap (sh 2 (Dv Γ)) (v 0), sh 2 (A Γ), sh 2 (f Γ), v 1]))
        (Term.lam treeTy (thunkRel P T (sh 2 (Ee Γ)) (sh 2 (dt Γ)) (sh 2 (Dv Γ)) (sh 2 (Rt Γ)) (v 1)
          (v 0))))
      let F (Γ : List Tree) : Term := Term.lam nat (Term.lam treeTy
        (pv [ap (sh 2 (Dv Γ)) (v 1), sh 2 (A Γ), sh 2 (f Γ), v 0]))
      let mono : Deducer := dAllI L (dImpI L (K.normLast fun Γ Φ ψ ↦
        allEs K (Φ.length - 1) inst (K.impE (K.byHyp hf) byLast) Γ Φ ψ))
      let fin (n₁ n₂ w : List Tree → Term) (rR r₂ : ℕ) : Deducer := fun Γ Φ ψ ↦
        let (a₁, a₂) := (Φ.length - 2, Φ.length - 1)
        K.conv (fun Γ ↦ S.add (n₁ Γ) (n₂ Γ)) w
          (linkK K "cataPara: stable" <|
            K.instN a₁ (fun _ ↦ v 0) (K.instN a₂ (fun _ ↦ v 0) K.byNorm))
          (linkK K "cataPara: related" <| fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ rR) .full) rR (K.conjE fun Γ Φ ψ ↦
              let (iLen, iRel) := (Φ.length - 2, Φ.length - 1)
              normHyps K [r₂] (fun Γ Φ ψ ↦
                dImpE L (Φ.length - 1) (K.byHyp iLen) (K.impE (K.byHyp iRel) byLast) Γ Φ ψ)
                Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
      K.cutThm "allMono" (fun Γ ↦ [cs Γ]) <| K.allEΓ (fun _ ↦ Term.lam treeTy φ) <| K.allEΓ Q <|
        K.impE (K.byHyp hAll) <| K.impE (linkK K "cataPara: the children's convergences" mono) <|
        fun Γ Φ ψ ↦
        let hQ := Φ.length - 1
        (K.cutThm "relatedConv" (fun Γ ↦ [cs Γ, F Γ, Rt Γ, Dv Γ, dt Γ, Ee Γ]) <|
          K.impE (linkK K "cataPara: the children" (K.byHyp hQ)) <|
          K.convE fun Γ₂ Φ₂ ψ₂ ↦
          let n₁ (Γ : List Tree) : Term := v (Γ.length - Γ₂.length + 1)
          let vs (Γ : List Tree) : Term := v (Γ.length - Γ₂.length)
          let (s₁, rR) := (Φ₂.length - 2, Φ₂.length - 1)
          dAllE L K.G K.E hf (tree Γ₂) (K.allEΓ (fun Γ ↦ call D.children [] [vs Γ]) <|
            K.convE fun Γ₃ Φ₃ ψ₃ ↦
            let n₂ (Γ : List Tree) : Term := v (Γ.length - Γ₃.length + 1)
            let w (Γ : List Tree) : Term := v (Γ.length - Γ₃.length)
            let (s₂, r₂) := (Φ₃.length - 2, Φ₃.length - 1)
            K.shift s₁ false n₂ (K.shift s₂ true n₁ (fin n₁ n₂ w rR r₂)) Γ₃ Φ₃ ψ₃) Γ₂ Φ₂ ψ₂)
          Γ Φ ψ
    let node : Deducer :=
      K.cutThm "cataParaAll" (fun Γ ↦ [v (Γ.length - 2)]) (K.impE dHyp fun Γ Φ ψ ↦
        let hAll := Φ.length - 1
        allIs L 6 (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
          linkK K "cataPara: a node" (body Γ₁ hAll (Φ₁.length - 1)) Γ₁ Φ₁ ψ₁) Γ Φ ψ)
    let d ← node [list treeTy, bitsTy] [Internal.roseHyp 0 1 φ]
      (Internal.roseNodeAt 2 treeTy bitsTy φ)
    pure (⟨0, [treeTy], [], φ⟩, nd (.roseIndHyp 2 0 1) [d]))

/-- The erasure of a structural recursion, at the result type's form {lit}`r`, the scrutinee's
{lit}`s` and the chain of its clauses {lit}`ch`: the kernel's fold of trees whose step sees the
node, at the suspended result, applied to the unit value. -/
def cataErasure (P : Prog) (r s ch : Term) : Term :=
  let d (n : String) : Term := pc P s!"Datatype.{n}" []
  let th := pc P "Datatype.thTy" [r]
  pc P "Datatype.sx2" [pc P "Datatype.sx4" [d "aPara", th,
    pc P "Datatype.sLam2" [d "aO", d "aT", d "aK", pc P "Datatype.sList" [th],
      pc P "Datatype.sLam1" [d "aU", d "aUnit", ch]], s], d "aUnitV"]

/-- The atoms of the erasure of a structural recursion ({name}`cataErasure`) around its parts. -/
def cataErasureAtoms (P : Prog) : List Term :=
  ["aPara", "aO", "aT", "aK", "aU", "aUnit", "aUnitV", "aLam", "aList", "aArrow"].map fun a ↦
    atomNameT (pc P s!"Datatype.{a}" [])

/-- The expansion of the numeral abbreviations at the erasure of a structural recursion
({name}`cataErasure`), its atoms not abbreviated, is the erasure at its parts' expansions. In the
context of the chain's, the scrutinee's and the result type's forms and the abbreviations. -/
def cataNums (P : Prog) (S : Defs) (T : Defs3) : Step :=
  let en (t : Term) : Term := pc P "Reader.expandNums" [v 3, t]
  builderEq "cataNums" P S [treeTy, treeTy, treeTy, list treeTy]
    ((cataErasureAtoms P).map fun a ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [a, v 3]])
    (en (cataErasure P (v 2) (v 1) (v 0))) (fun _ _ _ ↦ [.delta (T.argIdx 3)])
    (some (cataErasure P (en (v 2)) (en (v 1)) (en (v 0))))

/-- The fold of a structural recursion's kernel's form, at the type {lit}`th` and the terms
{lit}`f` and {lit}`x`. -/
def paraForm (P : Prog) (th f x : Term) : Term :=
  pc P "Datatype.sx4" [pc P "Datatype.aPara" [], th, f, x]

/-- The resolution of the parts of the erasure of a structural recursion ({name}`cataErasure`), one
at a time, present and absent: the abstractions over the node and the suspended results; the keyword
form of the fold, the type a reading and the terms resolved; and its application to the unit value,
whose name is in neither the scope nor the definitions' names. Each in the context of its parts, the
scope, the type abbreviations and the definitions' names. -/
def cataResLemmas (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let res : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule :=
    fun P ix E ↦ resolveRules P T ix E
  let none' : Term := pc P "Prelude.none" []
  let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
  let rs (tys names t sc : Term) : Term := pc P "Reader.resolve" [tys, names, t, sc]
  let L := list treeTy
  let unitN := atomNameT (pc P "Datatype.aUnitV" [])
  -- the type v0, the terms v1, v2, the scope v3, the type abbreviations v4, the names v5
  let Γp := [treeTy, treeTy, treeTy, L, L, L]
  let lhsP := rs (v 4) (v 5) (paraForm P (v 0) (v 1) (v 2)) (v 3)
  let rT := isSome (pc P "Reader.readType" [v 4, v 0])
  let (r₁, r₂) := (rs (v 4) (v 5) (v 1) (v 3), rs (v 4) (v 5) (v 2) (v 3))
  let lhsU := rs (v 4) (v 5) (pc P "Datatype.sx2" [paraForm P (v 0) (v 1) (v 2),
    pc P "Datatype.aUnitV" []]) (v 3)
  -- an abstraction over the name: the type v0, the body v1, the scope v2, the type abbreviations
  -- v3, the names v4
  let lam1 (name x : String) : List Step :=
    let lhs := rs (v 3) (v 4) (pc P "Datatype.sLam1" [pc P s!"Datatype.{x}" [], v 0, v 1]) (v 2)
    let body := isSome (rs (v 3) (v 4) (v 1)
      (consT treeTy (atomNameT (pc P s!"Datatype.{x}" [])) (v 2)))
    let rA := isSome (pc P "Reader.readType" [v 3, v 0])
    [eqUnder s!"{name}Res" P S [treeTy, treeTy, L, L, L] [] lhs res [] [rA, body],
      eqUnder s!"{name}None" P S [treeTy, treeTy, L, L, L] [] lhs res [body]]
  lam1 "lamO" "aO" ++ lam1 "lamK" "aK" ++
  [eqUnder "paraRes" P S Γp [] lhsP res [] [rT, isSome r₁, isSome r₂],
    eqUnder "paraNoType" P S Γp [] lhsP res [rT],
    eqUnder "paraNoStep" P S Γp [] lhsP res [isSome r₁] [rT],
    eqUnder "paraNoScrut" P S Γp [] lhsP res [isSome r₂] [rT, isSome r₁],
    eqUnder "paraUnitRes" P S Γp
      [Term.eq (pc P "Reader.indexOf" [unitN, v 3]) none',
        Term.eq (pc P "Reader.indexOf" [unitN, v 5]) none'] lhsU res [] [isSome lhsP],
    eqUnder "paraUnitNone" P S Γp [] lhsU res [isSome lhsP]]

/-- The resolution of the erasure of a structural recursion ({name}`cataErasure`) in a scope, the
unit value's name in neither the scope nor the definitions' names, the result type's form a reading
and the chain and the scrutinee resolved: the composition of the resolution lemmas
({name}`cataResLemmas`), innermost first. In the context of the chain's, the scrutinee's and the
result type's forms, the scope, the type abbreviations and the definitions' names, its left side in
the normal form of the walk's rules. -/
def cataResEq (P : Prog) (S : Defs) : Step :=
  ("cataResEq", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let L := list treeTy
    let Γ := [treeTy, treeTy, treeTy, L, L, L]
    let d (n : String) : Term := pc P s!"Datatype.{n}" []
    let at_ (i : ℕ) (Δ : List Tree) : Term := v (Δ.length - Γ.length + i)
    let (ch, sF, rF, sc, tys, names) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5)
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let rs (t sc : Term) (Δ : List Tree) : Term := pc P "Reader.resolve" [tys Δ, names Δ, t, sc]
    let th (Δ : List Tree) : Term := pc P "Datatype.thTy" [rF Δ]
    let lamU (Δ : List Tree) : Term := pc P "Datatype.sLam1" [d "aU", d "aUnit", ch Δ]
    let lamK (Δ : List Tree) : Term :=
      pc P "Datatype.sLam1" [d "aK", pc P "Datatype.sList" [th Δ], lamU Δ]
    let stepF (Δ : List Tree) : Term := pc P "Datatype.sLam1" [d "aO", d "aT", lamK Δ]
    let unitN := atomNameT (d "aUnitV")
    let scO (Δ : List Tree) : Term := consT treeTy (nodeName P) (sc Δ)
    let scK (Δ : List Tree) : Term := consT treeTy (resultsName P) (scO Δ)
    let lhs := pc P "Reader.resolve" [tys Γ, names Γ, cataErasure P (rF Γ) (sF Γ) (ch Γ), sc Γ]
    let passes : List Term := [isSome (pc P "Reader.readType" [tys Γ, rF Γ]),
      isSome (rs (ch Γ) (cataNames P (sc Γ)) Γ), isSome (rs (sF Γ) (sc Γ) Γ)]
    let hyps ← ([Term.eq (pc P "Reader.indexOf" [unitN, sc Γ]) (pc P "Prelude.none" []),
      Term.eq (pc P "Reader.indexOf" [unitN, names Γ]) (pc P "Prelude.none" [])] ++
        passes.map (truth P.o)).mapM fun h ↦
        (evalRw K.G K.E (K.rules []) .full Γ [] h).map Prod.fst
    let hyps := Internal.Logic.tt P.o :: hyps
    -- the passing tests' outcomes' equations, which the normal form of the right side reads
    let oks ← passes.mapM fun t ↦ do
      let (X, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (call D.lab [] [t])
      pure (Term.eq X (numeral 1))
    let instances : List (String × List Term) :=
      [("lamURes", [d "aUnit", ch Γ, scK Γ, tys Γ, names Γ]),
        ("lamKRes", [pc P "Datatype.sList" [th Γ], lamU Γ, scO Γ, tys Γ, names Γ]),
        ("lamORes", [d "aT", lamK Γ, sc Γ, tys Γ, names Γ]),
        ("paraRes", [th Γ, stepF Γ, sF Γ, sc Γ, tys Γ, names Γ]),
        ("paraUnitRes", [th Γ, stepF Γ, sF Γ, sc Γ, tys Γ, names Γ])]
    let Φ ← instances.foldlM (fun Φ (nm, σ) ↦ do
      let some (Internal.Entry.language thm) := E[ix nm]? | none
      let (l, r) ← Internal.eqParts (Internal.instTerm [] σ thm.concl)
      let (l', _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ l
      let (r', _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ r
      pure (Φ ++ [Term.eq l' r'])) (hyps ++ oks)
    let Kw : Kit := { K with more := walkRules ix E }
    let (l, _) ← evalRw Kw.G Kw.E (Kw.rules []) .full Γ [] lhs
    let (r, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ lhs
    let a : Internal.Thm := ⟨0, Γ, hyps, Term.eq l r⟩
    let prem : Deducer := resPrem K (fun Δ ↦ pc P "Reader.readType" [tys Δ, rF Δ]) 3
    let use (nm : String) (σ : List Term) (k : Deducer) : Deducer := fun Γ' Φ ψ ↦ do
      let some (Internal.Entry.language thm) := E[ix nm]? | none
      linkK K s!"cataResEq: {nm}" (applyThm K nm (fun Δ ↦ σ.map (sh (Δ.length - Γ.length)))
        (thm.hyps.map fun _ ↦ prem)
        (linkK K s!"cataResEq: {nm}'s equation" (normLastK K k))) Γ' Φ ψ
    let sides : Deducer := linkK K "cataResEq: the sides" fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ) Γ (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let at' (t : Term) (Δ : List Tree) : Term := sh (Δ.length - Γ.length) t
    let decisions (k : Deducer) : Deducer := passes.zipIdx.foldr (fun (t, i) k ↦
      decideIn K (at' t) (linkK K s!"cataResEq: passing test {i} false" (K.hypFalse (3 + i))) k) k
    let some dv := decisions (instances.foldr (fun (nm, σ) k ↦ use nm σ k) sides)
        a.ctx a.hyps a.concl
      | dbgTrace "cataResEq: not proved" fun _ ↦ none
    pure (a, dv))

/-- The erasure of a structural recursion ({name}`cataErasure`) resolved, its parts are: each
absent refuting the resolution by the absences' lemmas ({name}`cataResLemmas`). In the context of
{name}`cataResEq`. -/
def cataParts (P : Prog) (S : Defs) : Step :=
  ("cataParts", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let L := K.L
    let Lt := list treeTy
    let Γ := [treeTy, treeTy, treeTy, Lt, Lt, Lt]
    let d (n : String) : Term := pc P s!"Datatype.{n}" []
    let at_ (i : ℕ) (Δ : List Tree) : Term := v (Δ.length - Γ.length + i)
    let (ch, sF, rF, sc, tys, names) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5)
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let rs (t sc : Term) (Δ : List Tree) : Term := pc P "Reader.resolve" [tys Δ, names Δ, t, sc]
    let th (Δ : List Tree) : Term := pc P "Datatype.thTy" [rF Δ]
    let lamU (Δ : List Tree) : Term := pc P "Datatype.sLam1" [d "aU", d "aUnit", ch Δ]
    let lamK (Δ : List Tree) : Term :=
      pc P "Datatype.sLam1" [d "aK", pc P "Datatype.sList" [th Δ], lamU Δ]
    let stepF (Δ : List Tree) : Term := pc P "Datatype.sLam1" [d "aO", d "aT", lamK Δ]
    let scO (Δ : List Tree) : Term := consT treeTy (nodeName P) (sc Δ)
    let scK (Δ : List Tree) : Term := consT treeTy (resultsName P) (scO Δ)
    let conj := Internal.Logic.conj P.o
    let rT (Δ : List Tree) : Term := isSome (pc P "Reader.readType" [tys Δ, rF Δ])
    let chT (Δ : List Tree) : Term := isSome (rs (ch Δ) (cataNames P (sc Δ)) Δ)
    let sT (Δ : List Tree) : Term := isSome (rs (sF Δ) (sc Δ) Δ)
    let a : Internal.Thm := ⟨0, Γ, [Internal.Logic.tt P.o, truth P.o (isSome (rs
        (cataErasure P (rF Γ) (sF Γ) (ch Γ)) (sc Γ) Γ))],
      conj (truth P.o (rT Γ)) (conj (truth P.o (chT Γ)) (truth P.o (sT Γ)))⟩
    let negated : Deducer := dImpI K.L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let prem : Deducer := fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦
      (K.norm dHyp Γ Φ ψ).orElse fun _ ↦ negated Γ Φ ψ
    let use (nm : String) (σ : List Tree → List Term) (k : Deducer) : Deducer := fun Γ' Φ ψ ↦ do
      let some (Internal.Entry.language thm) := E[ix nm]? | none
      linkK K s!"cataParts: {nm}" (applyThm K nm σ (thm.hyps.map fun _ ↦ prem)
        (normLastK K k)) Γ' Φ ψ
    let σp (Γ : List Tree) : List Term := [th Γ, stepF Γ, sF Γ, sc Γ, tys Γ, names Γ]
    let refute : Deducer := linkK K "cataParts: refuted" (K.hypFalse 1)
    let viaFold (k : Deducer) : Deducer := use "paraUnitNone" σp k
    let stepNone (k : Deducer) : Deducer :=
      use "lamUNone" (fun Γ ↦ [d "aUnit", ch Γ, scK Γ, tys Γ, names Γ]) <|
      use "lamKNone" (fun Γ ↦ [pc P "Datatype.sList" [th Γ], lamU Γ, scO Γ, tys Γ, names Γ]) <|
      use "lamONone" (fun Γ ↦ [d "aT", lamK Γ, sc Γ, tys Γ, names Γ]) k
    let stepRes (k : Deducer) : Deducer :=
      use "lamURes" (fun Γ ↦ [d "aUnit", ch Γ, scK Γ, tys Γ, names Γ]) <|
      use "lamKRes" (fun Γ ↦ [pc P "Datatype.sList" [th Γ], lamU Γ, scO Γ, tys Γ, names Γ]) <|
      use "lamORes" (fun Γ ↦ [d "aT", lamK Γ, sc Γ, tys Γ, names Γ]) k
    let some dv := (decideIn K rT (use "paraNoType" σp <| viaFold refute) <|
        decideIn K chT (stepNone <| use "paraNoStep" σp <| viaFold refute) <|
        decideIn K sT (stepRes <| use "paraNoScrut" σp <| viaFold refute) <|
        linkK K "cataParts: the parts" (dConjI L
          (linkK K "cataParts: the reading" (K.solve 3))
          (dConjI L (K.solve 3) (K.solve 3)))) a.ctx a.hyps a.concl
      | dbgTrace "cataParts: not proved" fun _ ↦ none
    pure (a, dv))

/-- The development of the soundness at a structural recursion. -/
def cataSoundDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [relatedCons P S T, relatedConv P S T,
    roseAllFor P S "cataParaAll" (cataParaφ (walkProg P) S T), cataPara P S T,
    cataNums P S T] ++ cataResLemmas P S T ++ [cataResEq P S, cataParts P S]

/-- The soundness at a structural recursion, after the chain of its clauses. -/
def cataSoundCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := caseNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (caseDev P S T).map (·.1) ++ (clausesDev P S T).map (·.1) ++
    (caseSoundDev P S T).map (·.1) ++ (cataDev P S T).map (·.1) ++
    (cataClausesDev P S T).map (·.1) ++ (cataChainDev P S T).map (·.1)) "datatype-cata-sound"
    (cataSoundDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
