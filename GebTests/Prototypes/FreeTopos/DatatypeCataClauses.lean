/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeCata
public meta import GebTests.Prototypes.FreeTopos.DatatypeCata -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at a structural recursion's clauses

The soundness of the datatype language's stage-1 compiler at the clauses of a structural recursion:
a clause, the suspended results and the children bound around the walk of its fields.

## Main definitions

* {lit}`cataClausesCertificates` — the development, stored as the certificate
  {lit}`datatype-cata-clauses`.

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

/-- The named context's entry of a structural recursion's unit argument. -/
def unitEntry (P : Prog) : Term :=
  pc P "Typing.abbr" [pc P "Typing.boundName" [pc P "Typing.kwUnitArg" []], pc P "Typing.tyUnit" []]

/-- The named context's entry of a structural recursion's children's suspended results, at the
result type {lit}`R`. -/
def resultsEntry (P : Prog) (R : Term) : Term :=
  pc P "Typing.abbr" [pc P "Typing.boundName" [pc P "Typing.kwResults" []],
    pc P "Typing.tyList" [thunkTy P R]]

/-- The named context's entry of a structural recursion's node. -/
def nodeEntry (P : Prog) : Term :=
  pc P "Typing.abbr" [pc P "Typing.boundName" [pc P "Typing.kwNode" []], pc P "Typing.tyT" []]

/-- The named context a structural recursion's clauses are typed in: the recursion's entries
before the context {lit}`inner`, at the result type {lit}`R`. -/
def cataScope (P : Prog) (R inner : Term) : Term :=
  consT treeTy (unitEntry P) (consT treeTy (resultsEntry P R) (consT treeTy (nodeEntry P) inner))

/-- The name of a structural recursion's node, as the reader reads it. -/
def nodeName (P : Prog) : Term := atomNameT (pc P "Datatype.aO" [])

/-- The name of a structural recursion's children's suspended results, as the reader reads it. -/
def resultsName (P : Prog) : Term := atomNameT (pc P "Datatype.aK" [])

/-- The name of a structural recursion's unit argument, as the reader reads it. -/
def unitName (P : Prog) : Term := atomNameT (pc P "Datatype.aU" [])

/-- The reader's scope of a structural recursion's clauses before the scope {lit}`sc`. -/
def cataNames (P : Prog) (sc : Term) : Term :=
  consT treeTy (unitName P) (consT treeTy (resultsName P) (consT treeTy (nodeName P) sc))

/-- The first component of the erasure's pair of a clause: the default result suspended, at the
default's form {lit}`dr`. -/
def defaultThunk (P : Prog) (dr : Term) : Term :=
  pc P "Datatype.sLam1" [pc P "Datatype.aU" [], pc P "Datatype.aUnit" [], dr]

/-- The erasure's pair of a clause: the default suspended and the children's suspended results. -/
def clausePair (P : Prog) (dr : Term) : Term :=
  pc P "Datatype.sx3" [pc P "Datatype.aPair" [], defaultThunk P dr, pc P "Datatype.aK" []]

/-- The erasure's application of the children primitive to the recursion's node. -/
def childrenOfO (P : Prog) : Term :=
  pc P "Datatype.sx2" [pc P "Datatype.aChildren" [], pc P "Datatype.aO" []]

/-- The erasure's bindings of a structural recursion's clause around a rest {lit}`rest`, at the
result type's form {lit}`r` and the default's form {lit}`dr`: the split's name to the pair of the
default suspended and the suspended results, the children remaining to the node's children. -/
def cataClauseStep (P : Prog) (r dr rest : Term) : Term :=
  let (aQ, aC, aT) := (pc P "Datatype.aQ" [], pc P "Datatype.aC" [], pc P "Datatype.aT" [])
  pc P "Datatype.sLet" [aQ, pc P "Datatype.splitTy" [r], clausePair P dr,
    pc P "Datatype.sLet" [aC, pc P "Datatype.sList" [aT], childrenOfO P, rest]]

/-- The atoms a structural recursion's clause's bindings write beyond its fragments'
({name}`cataAtoms`), each with its exclusion's lemma's name. -/
def clauseExcluded (P : Prog) : List (Term × String) :=
  [(nodeName P, "nodeExcluded"), (resultsName P, "resultsExcluded")]

/-- The expansion of the numeral abbreviations at the erasure's pair of a clause and at its
application of the children primitive, their atoms not abbreviated: the pair at the default's
expansion, the application itself. In the context of the default's form and the abbreviations. -/
def clauseNums (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let en (t : Term) : Term := pc P "Reader.expandNums" [v 1, t]
  let tests := (cataAtoms P ++ [nodeName P, resultsName P, childrenName P]).map fun a ↦
    pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [a, v 1]]
  let step3 : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule :=
    fun _ _ _ ↦ [.delta (T.argIdx 3)]
  let Γ := [treeTy, list treeTy]
  [builderEq "clausePairNums" P S Γ tests (en (clausePair P (v 0))) step3
      (some (clausePair P (en (v 0)))),
    builderEq "childrenONums" P S Γ tests (en (childrenOfO P)) step3 (some (childrenOfO P))]

/-- The outcomes of a structural recursion's clause's bindings' resolution. -/
inductive ClauseOutcome where
  /-- The parts present. -/
  | present
  /-- The result type's form without a reading. -/
  | noType
  /-- The default unresolved beneath the unit's binder. -/
  | noDefault
  /-- The rest unresolved beneath the two bindings. -/
  | noRest

/-- The scope of a structural recursion's clause's rest before the scope {lit}`sc`: the names of
the children remaining and of the split, then the recursion's. -/
def clauseNames (P : Prog) (sc : Term) : Term :=
  consT treeTy (fieldsName P) (consT treeTy (splitName P) (cataNames P sc))

/-- The resolution of a structural recursion's clause's bindings ({name}`cataClauseStep`), in the
scope of the recursion's names ({name}`cataNames`): its left side in the normal form of the walk's
rules, its right side by the reader's case of bindings and steps unfolded. Present, the children
primitive's name in neither the scope's tail nor the definitions' names, the result type's form a
reading and the default and the rest resolved, the application of the two bindings' abstractions;
absent, where the reading, the rest's or, the rest resolved, the default's resolution is, none. In
the context of the rest, the scope's tail, the type abbreviations, the definitions' names, the
result type's form and the default's form. -/
def cataResAt (name : String) (out : ClauseOutcome) (P : Prog) (S : Defs) (T : Defs3) : Step :=
  (name, fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let (rest, sc, tys, names, rF, drF) := (v 0, v 1, v 2, v 3, v 4, v 5)
    let Γ := [treeTy, list treeTy, list treeTy, list treeTy, treeTy, treeTy]
    let lhs := pc P "Reader.resolve" [tys, names, cataClauseStep P rF drF rest, cataNames P sc]
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let reading := isSome (pc P "Reader.readType" [tys, rF])
    let dfltR := pc P "Reader.resolve" [tys, names, drF, consT treeTy (unitName P) (cataNames P sc)]
    let restR := pc P "Reader.resolve" [tys, names, rest, clauseNames P sc]
    let (tests, passes) : List Term × List Term := match out with
      | .present => ([isSome (pc P "Reader.indexOf" [childrenName P, sc]),
          isSome (pc P "Reader.indexOf" [childrenName P, names])],
          [reading, isSome dfltR, isSome restR])
      | .noType => ([reading], [])
      | .noDefault => ([isSome dfltR, isSome (pc P "Reader.indexOf" [childrenName P, sc]),
          isSome (pc P "Reader.indexOf" [childrenName P, names])], [reading, isSome restR])
      | .noRest => ([isSome restR], [reading])
    let labelEq (t X : Term) : Option Term := do
      let (L, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (call D.lab [] [t])
      pure (Term.eq L X)
    let fails ← tests.mapM fun t ↦ labelEq t bnilT
    let oks ← passes.mapM fun t ↦ labelEq t (numeral 1)
    -- past a first hypothesis of truth, which supplies no rule
    let hyps := Internal.Logic.tt P.o :: tests.map (notTest P.o) ++ passes.map (truth P.o)
    let Φ := Internal.Logic.tt P.o :: fails ++ oks
    let Kw : Kit := { K with more := walkRules ix E }
    let (l, _) ← evalRw Kw.G Kw.E (Kw.rules []) .full Γ [] lhs
    let unfold := resolveRules P T ix E
    let (r, _) ← evalRw K.G K.E (K.rules Φ ++ unfold) .full Γ Φ lhs
    let a : Internal.Thm := ⟨0, Γ, hyps, Term.eq l r⟩
    let at_ (t : Term) (Δ : List Tree) : Term := sh (Δ.length - Γ.length) t
    let decisions : Deducer → Deducer := fun k ↦
      tests.zipIdx.foldr (fun (t, i) k ↦
        decideIn K (at_ t) k (linkK K s!"{name}: test {i} true" fun Γ Φ ψ ↦
          dImpE K.L (1 + i) (K.solve 3) (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ))
        (passes.zipIdx.foldr (fun (t, i) k ↦
          decideIn K (at_ t) (linkK K s!"{name}: passing test {i} false"
            (K.hypFalse (1 + tests.length + i))) k) k)
    let some d := decisions (linkK K s!"{name}: the sides" fun Γ Φ ψ ↦
        dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold) Γ
          (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The kernel's terms of a structural recursion's clause's bindings' values, the pair's and the
children's, read off the present resolution on the right side of {lit}`cataClauseRes`, in its
context. -/
def clauseTerms (E : Array Internal.Entry) (ix : String → ℕ) : Option (Term × Term) := do
  let y ← boundTerm E ix "cataClauseRes"
  let [f, e] ← nodeKidsT y | none
  let [_, rB] ← nodeKidsT f | none
  let [_, e₂] ← nodeKidsT rB | none
  pure (e, e₂)

/-- The pair of a clause's binding's kernel's term ({name}`clauseTerms`) converges, in the
environment of a unit value, a list value of suspended results and a tree's quotation, to the value
its evaluation normalizes to at a level, the list value its second component. In the context of
{lit}`cataClauseRes`, then the environment's tail, the tree, the suspended results' value, the unit
value and the relation's context. -/
def clausePairConv (P : Prog) (S : Defs) : Step :=
  ("clausePairConv", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, evalMore⟩
    let (e, _) ← clauseTerms E ix
    let Γ := [treeTy, list treeTy, list treeTy, list treeTy, treeTy, treeTy,
      list treeTy, treeTy, treeTy, treeTy, Defs3.ctxTy]
    let env := consT treeTy (v 9) (consT treeTy (v 8) (consT treeTy
      (pc P "Eval.valQuote" [v 7]) (v 6)))
    let lv : Term := (5 : ℕ).rec zeroN fun _ t ↦ succN t
    let (wrapped, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (S.evN (Term.fst (v 10)) lv env e)
    let [val] ← nodeKidsT wrapped | none
    let a : Internal.Thm := ⟨0, Γ, [], S.conv (Term.lam nat (S.evN (Term.fst (v 11)) (v 0)
      (sh 1 env) (sh 1 e))) (Term.lam treeTy (Term.eq (v 0) (sh 1 val)))⟩
    let some d := dConv K.L K.G K.E S lv val
        (linkK K "clausePairConv stable" K.byNorm)
        (linkK K "clausePairConv value" (K.norm K.byNorm))
        a.ctx a.hyps a.concl
      | dbgTrace s!"clausePairConv: not proved {showT val}" fun _ ↦ none
    pure (a, d))

/-- The children of a clause's binding's kernel's term ({name}`clauseTerms`) converge, in the
environment of the split's value, a unit value, a list value of suspended results and a tree's
quotation, to the list value of the quotations of the tree's children. In the context of the
environment's tail, the tree, the suspended results' value, the unit value, the split's value and
the relation's context. -/
def clauseChildrenConv (P : Prog) (S : Defs) : Step :=
  ("clauseChildrenConv", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, (evalPrims ++ ["nthThree4"]).filter
      fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let (_, e₂) ← clauseTerms E ix
    let Γ := [list treeTy, treeTy, treeTy, treeTy, treeTy, Defs3.ctxTy]
    let env := consT treeTy (v 4) (consT treeTy (v 3) (consT treeTy (v 2) (consT treeTy
      (pc P "Eval.valQuote" [v 1]) (v 0))))
    let value := treeList P (quotesT P (call D.children [] [v 1]))
    let a : Internal.Thm := ⟨0, Γ, [], S.conv (Term.lam nat (S.evN (Term.fst (v 6)) (v 0)
      (sh 1 env) e₂)) (Term.lam treeTy (Term.eq (v 0) (sh 1 value)))⟩
    let lv : Term := (5 : ℕ).rec zeroN fun _ t ↦ succN t
    let some d := dConv K.L K.G K.E S lv value
        (linkK K "clauseChildrenConv stable" K.byNorm)
        (linkK K "clauseChildrenConv value" (K.norm K.byNorm))
        a.ctx a.hyps a.concl
      | dbgTrace s!"clauseChildrenConv: not proved {showT e₂}" fun _ ↦ none
    pure (a, d))

/-- The context of a structural recursion's clause: a case analysis's ({name}`clauseCtx`), then, as
in {name}`cataWalkCtx`, the datatype's atom v11, the result type v12, the result type's form v13 and
the default result's form v14. -/
def cataClauseCtx (T : Defs3) : List Tree :=
  clauseCtx T ++ [treeTy, treeTy, treeTy, treeTy]

/-- The erasure's bindings of a structural recursion's clause's variables, of metadata {lit}`md`
around its body {lit}`b`, at the result type's form {lit}`r` and the default's form {lit}`dr`: the
walk's erasure ({lit}`WalkParts.er`) at the metadata's lists. -/
def cataBinds (P : Prog) (w : WalkParts) (md b r dr : Term) : Term :=
  Term.subst w.er fun i ↦ match i with
    | 0 => metaAt P md 1
    | 1 => b
    | 3 => metaAt P md 2
    | 13 => r
    | 14 => dr
    | _ => Term.star

/-- The statement of a structural recursion's clause, at {name}`cataClauseCtx`: where the relation's
markers are the typing environment's, no numeral abbreviation names a keyword, the clause's entries'
variables' characters are fixed and their flags those the expansion writes, the body's erasure is
sound at its typing, the numeral abbreviations are coherent with the typing environment, the
definitions' names none a primitive's, for all named contexts,
environments and kernel's contexts beneath the recursion's entries, suspended results, the results'
type and unit values, if the clause's typing is present in the named context extended by the
recursion's entries, the constructor's test holds of the memberships of the node's children, the
results are as many as the children and related, the environment of the unit value, the results'
list value and the node's quotation is related to that context, whose names are admitted, the
clause's erasure resolves in its scope, of a type in the kernel's context, and the children
primitive's name is neither in the context's scope nor a definition's, the resolution converges to
a value related at the clause's type. -/
def cataClauseφ (P : Prog) (S : Defs) (T : Defs3) (w : WalkParts) : Term :=
  let o := P.o
  let all (A : Tree) (t : Term) : Term := Internal.Logic.all o A (Term.lam A t)
  let imp := Internal.Logic.imp o
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let childT := (primT Kernel.Prim.child).getD Term.star
  -- beneath the six quantifiers: the named context v5, the environment v4, the kernel's context
  -- v3, the results v2, the results' type v1 and the unit value v0; the clause's context's
  -- variables shifted by 6
  let q (i : ℕ) : Term := v (i + 6)
  let cx := cataScope P (q 12) (v 5)
  let env := consT treeTy (v 0) (consT treeTy (pc P "Eval.ofList" [v 1, v 2])
    (consT treeTy (pc P "Eval.valQuote" [q 3]) (v 4)))
  let tyC := pc P "Typing.cataFields" [q 5, q 11, q 12, q 4, q 0, q 2, cx]
  let ms := pc P "Typing.envMs" [q 5]
  let mem := Term.lam treeTy (pc P "Typing.memberships" [sh 1 ms, v 0])
  let fts := call D.children [] [apps childT [q 4, leafT (numeral 1)]]
  let ts := call D.children [] [q 3]
  let okC := Term.app (foldrAt (sh 6 w.ok) fts) (mapListsT mem ts)
  let kw := pc P "Reader.resolve" [q 7, q 9, pc P "Reader.expandNums" [q 8,
    cataClauseStep P (q 13) (q 14) (cataBinds P w (q 0) (q 1) (q 13) (q 14))],
    scopeOf P (q 8) cx]
  let unindexed (t : Term) : Term :=
    notTest o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [childrenName P, t]])
  let fixedE : Term := fixedEntry P (v 8)
  let flagE : Term := flagEntry P
  imp (Term.eq (Term.snd (v 10)) (pc P "Typing.envMs" [v 5])) <| imp (T.kwsT (v 8)) <|
    imp (S.allL fixedE (metaAt P (v 0) 1)) <| imp (S.allL fixedE (metaAt P (v 0) 2)) <|
    imp (S.allL flagE (metaAt P (v 0) 1)) <| imp (S.allL flagE (metaAt P (v 0) 2)) <|
    imp (bodyφ P S T 0 (v 1) (v 2)) <| imp (T.numsT (v 5) (v 8)) <| imp (T.namesT (v 9)) <|
    all (list treeTy) <| all (list treeTy) <| all (list treeTy) <| all (list treeTy) <|
    all treeTy <| all treeTy <|
    imp (isSomeT tyC) <| imp (truth o okC) <| imp (lenEqT P ts (v 2)) <|
    imp (relatedT P T (q 5) (q 11) (q 10) (q 12) ts (v 2)) <|
    imp (T.envT (q 10) cx env) <| imp (T.cxT (q 5) cx) <| imp (isSomeT kw) <|
    imp (isSomeT (pc P "Check.typeIn" [q 6, v 3, get kw])) <|
    imp (unindexed (scopeOf P (q 8) (v 5))) <| imp (unindexed (q 9)) <|
    S.conv (Term.lam nat (S.evN (Term.fst (sh 1 (q 10))) (v 0) (sh 1 env) (sh 1 (get kw))))
      (T.relT (q 10) (get tyC))

/-- The soundness at a structural recursion's clause ({name}`cataClauseφ`): the atoms' decisions and
the builders' expansions; the clause's resolution by {name}`cataResAt`, the parts present, else the
resolution refuted; the kernel's typing of the bindings split ({lit}`letTyped`), and their
convergence ({lit}`letConv`), the pair's by {name}`clausePairConv` and the children's by
{name}`clauseChildrenConv`, the rest's in the environment extended by their values by the walk
({name}`cataWalk`) at the clause. -/
def cataClause (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cataClause", fun ix E ↦ do
    let P := cataVarProg P
    let w ← cataWalkParts ⟨P, S, E, ix, []⟩ T
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let a : Internal.Thm := ⟨0, cataClauseCtx T, [], cataClauseφ P S T w⟩
    let steps : List Internal.NormRule :=
      ["Typing.bindRest", "Typing.bindVar", "Reader.numeral"].map fun nm ↦ .delta (P.idx nm)
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let byStep (h : ℕ) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ steps) .full) h
        (dRwBy (evalRw K.G K.E (K.rules Φ ++ steps) .full) dHyp) Γ Φ ψ
    let hypOr (h : ℕ) : Deducer := fun Γ Φ ψ ↦ (K.byHyp h Γ Φ ψ).orElse fun _ ↦
      (K.solve 3 Γ Φ ψ).orElse fun _ ↦ normHyps K [h] (K.solve 3) Γ Φ ψ
    let (hTy, hOk, hLen, hRel, hEnv, hCx, hRes, hKer, hNs, hNn) :=
      (15, 16, 17, 18, 19, 20, 21, 22, 23, 24)
    let negated : Deducer := dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let (drF, rF, Rty, dt, R, names, nums, tys, E', c, t, b, md) :=
      (atPos 0, atPos 1, atPos 2, atPos 3, atPos 4, atPos 5, atPos 6, atPos 7, atPos 9, atPos 10,
        atPos 11, atPos 13, atPos 14)
    let (inner, env0, rs, Ar, u) := (atPos 15, atPos 16, atPos 18, atPos 19, atPos 20)
    let (aQ, aC, aT) := (pc P "Datatype.aQ" [], pc P "Datatype.aC" [], pc P "Datatype.aT" [])
    let childT ← primT Kernel.Prim.child
    let en (Γ : List Tree) (x : Term) : Term := pc P "Reader.expandNums" [nums Γ, x]
    let binds (Γ : List Tree) : Term := cataBinds P w (md Γ) (b Γ) (rF Γ) (drF Γ)
    let rest₁ (Γ : List Tree) : Term :=
      pc P "Datatype.sLet" [aC, pc P "Datatype.sList" [aT], childrenOfO P, binds Γ]
    -- the expansions of the closed builders, of the fragments, then of the bindings
    let closedEqs (k : Deducer) : Deducer :=
      ["aTNums", "aCNums", "listTNums"].foldr (fun nm k ↦
        applyThm K nm (fun Γ ↦ [nums Γ]) ((walkAtoms P).map fun _ ↦ negated) <|
          normLastK K k) <|
      ["aQNums", "splitTyNums"].foldr (fun nm k ↦
        applyThm K nm (fun Γ ↦ [rF Γ, drF Γ, nums Γ]) ((cataAtoms P).map fun _ ↦ negated) <|
          normLastK K k) <|
      ["clausePairNums", "childrenONums"].foldr (fun nm k ↦
        applyThm K nm (fun Γ ↦ [drF Γ, nums Γ])
          ((cataAtoms P ++ [nodeName P, resultsName P, childrenName P]).map fun _ ↦ negated) <|
          normLastK K k) k
    let letEqs (k : Deducer) : Deducer :=
      applyThm K "letNums" (fun Γ ↦ [binds Γ, childrenOfO P, pc P "Datatype.sList" [aT], aC,
        nums Γ]) [negated] <| normLastK K <|
      applyThm K "letNums" (fun Γ ↦ [rest₁ Γ, clausePair P (drF Γ),
        pc P "Datatype.splitTy" [rF Γ], aQ, nums Γ]) [negated] <| normLastK K k
    let scope₀ (Γ : List Tree) : Term := scopeOf P (nums Γ) (inner Γ)
    let σres (Γ : List Tree) : List Term :=
      [en Γ (binds Γ), scope₀ Γ, tys Γ, names Γ, en Γ (rF Γ), en Γ (drF Γ)]
    let refuted (nm : String) (ps : List Deducer) : Deducer :=
      linkK K s!"cataClause: {nm}" <| applyThm K nm σres ps <| normLastK K (K.hypFalse hRes)
    let solved : Deducer := K.solve 3
    let readingR (Γ : List Tree) : Term := pc P "Reader.readType" [tys Γ, en Γ (rF Γ)]
    let dfltR (Γ : List Tree) : Term := pc P "Reader.resolve" [tys Γ, names Γ, en Γ (drF Γ),
      consT treeTy (unitName P) (cataNames P (scope₀ Γ))]
    let restR (Γ : List Tree) : Term := pc P "Reader.resolve" [tys Γ, names Γ, en Γ (binds Γ),
      clauseNames P (scope₀ Γ)]
    let isSome (x : Term) : Term := pc P "Prelude.isSome" [x]
    let decisions (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ isSome (readingR Γ)) (refuted "cataClauseNoType" [solved, negated]) <|
      decideIn K (fun Γ ↦ isSome (restR Γ))
        (refuted "cataClauseNoRest" [solved, negated, solved]) <|
      decideIn K (fun Γ ↦ isSome (dfltR Γ)) (refuted "cataClauseNoDefault"
        [solved, negated, K.byHyp hNs, K.byHyp hNn, solved, solved]) <|
      applyThm K "cataClauseRes" σres
        [solved, K.byHyp hNs, K.byHyp hNn, solved, solved, solved] <| normLastK K k
    let qSplit (Γ : List Tree) : Term := splitEntry P (Rty Γ)
    let cxS (Γ : List Tree) : Term := cataScope P (Rty Γ) (inner Γ)
    let kvT (Γ : List Tree) : Term := pc P "Eval.ofList" [Ar Γ, rs Γ]
    let envS (Γ : List Tree) : Term := consT treeTy (u Γ) (consT treeTy (kvT Γ)
      (consT treeTy (pc P "Eval.valQuote" [t Γ]) (env0 Γ)))
    let ts (Γ : List Tree) : Term := call D.children [] [t Γ]
    let fts (Γ : List Tree) : Term := call D.children [] [apps childT [c Γ, leafT (numeral 1)]]
    let qY (Γ : List Tree) : Term := treeList P (quotesT P (ts Γ))
    let fieldsNm : Term := pc P "Typing.boundName" [pc P "Typing.kwFields" []]
    let splitNm : Term := pc P "Typing.boundName" [pc P "Typing.kwSplit" []]
    let isQ (q : List Tree → Term) (Γ : List Tree) : Term :=
      Term.lam treeTy (Term.eq (v 0) (sh 1 (q Γ)))
    let present : Deducer := linkK K "cataClause: the parts resolved" fun Γ₀ Φ ψ ↦ do
      let (g, kc, x) ← apps3Of (P.idx "Check.typeIn") (← Φ[hKer]?)
      let (y, _) ← evalRw K.G K.E (K.rules Φ) .full Γ₀ Φ x
      let [f, e] ← nodeKidsT y | dbgTrace "cataClause: the term" fun _ ↦ none
      let [B, rB] ← nodeKidsT f | dbgTrace "cataClause: the abstraction" fun _ ↦ none
      let [f₂, e₂] ← nodeKidsT rB | dbgTrace "cataClause: the second term" fun _ ↦ none
      let [B₂, rB₂] ← nodeKidsT f₂ | dbgTrace "cataClause: the second abstraction" fun _ ↦ none
      let [Pg, F] := ψ.children | dbgTrace "cataClause: the goal" fun _ ↦ none
      let [body] := F.children | none
      let [f₁, _] := body.children | none
      let [fs, env] := f₁.children | none
      let [lvl] := fs.children | none
      let [_, dR] := lvl.children | none
      let [Rt] := dR.children | none
      let lower (z : Term) : Term := Term.subst z fun j ↦ v (j - 1)
      let (Rt, env) := (lower Rt, lower env)
      let wk (z : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) z
      -- the pair's convergence's instance and value, its first component the walk's
      let σp (Γ : List Tree) : List Term :=
        [en Γ (binds Γ), scope₀ Γ, tys Γ, names Γ, en Γ (rF Γ), en Γ (drF Γ), env0 Γ, t Γ, kvT Γ,
          u Γ, R Γ]
      let some (Internal.Entry.language thP) := E[ix "clausePairConv"]? | none
      let [Qp, _] := (Internal.instTerm [] (σp Γ₀) thP.concl).children
        | dbgTrace "cataClause: the pair's statement" fun _ ↦ none
      let [eqV] := Qp.children | none
      let (_, val) ← Internal.eqParts eqV
      let val := lower val
      let [first, _] ← nodeKidsT val | dbgTrace s!"cataClause: the value {showT val}" fun _ ↦ none
      -- the walk at the clause
      let walkAt (iTr : ℕ) : Deducer :=
        let envW (Γ : List Tree) : Term := consT treeTy (wk val Γ) (envS Γ)
        let cxW (Γ : List Tree) : Term := consT treeTy (qSplit Γ) (cxS Γ)
        let kcW (Γ : List Tree) : Term := consT treeTy (wk B Γ) (wk kc Γ)
        let KL : Kit := { K with more := K.more ++ lookupEqNames.filter fun nm ↦ 0 < ix nm }
        let implBound (msg : String) : Deducer := linkK K s!"cataClause: {msg} bound"
          fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ KL.solve 3 Γ Φ ψ
        let KN : Kit := { KL with more := KL.more ++ ["nthOne2", "nthOne3", "nthOne4", "nthOne5"] }
        let lookupOk : Deducer := fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ KN.solve 3 Γ Φ ψ
        let envOk : Deducer :=
          applyThm K "envTConsImpl" (fun Γ ↦ [qY Γ, fieldsEntry P, envW Γ, cxW Γ, R Γ])
            [linkK K "cataClause: the split's entry related" <|
              applyThm K "envTConsImpl" (fun Γ ↦ [wk val Γ, qSplit Γ, envS Γ, cxS Γ, R Γ])
                [hypOr hEnv, implBound "the split's name"] byLast,
              implBound "the children's name"] byLast
        let cxOk : Deducer :=
          let impl : Deducer := fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ KL.solve 3 Γ Φ ψ
          let consAt (ty : List Tree → Term) (n : Term) (cxT : List Tree → Term) (prev : Deducer) :
              Deducer := fun Γ Φ ψ ↦
            let cons : Deducer := applyThm K "cxTCons" (fun Γ ↦ [ty Γ, n, E' Γ, cxT Γ])
              [impl, prev] byLast
            decideIn K (fun Γ ↦ pc P "Typing.nameOk" [E' Γ, n]) cons cons Γ Φ ψ
          consAt (fun _ ↦ pc P "Typing.tyList" [pc P "Typing.tyT" []]) fieldsNm cxW
            (consAt (fun Γ ↦ pc P "Typing.tyProd" [thunkTy P (Rty Γ),
                pc P "Typing.tyList" [thunkTy P (Rty Γ)]]) splitNm cxS (hypOr hCx))
        K.cutThm "cataWalk" (fun Γ ↦ walkInst P (fun i ↦ atPos (14 - i) Γ) ++
            [dt Γ, Rty Γ, rF Γ, drF Γ]) <|
          K.impE (linkK K "cataClause: the markers" fun Γ Φ ψ ↦
            (dHyp Γ Φ ψ).orElse fun _ ↦ K.byNorm Γ Φ ψ) <|
          K.impE (linkK K "cataClause: the keywords" (K.byHyp 1)) <|
          K.impE (linkK K "cataClause: the variables' characters" (K.byHyp 2)) <|
          K.impE (linkK K "cataClause: the remaining variables' characters" (K.byHyp 3)) <|
          K.impE (linkK K "cataClause: the variables' flags" (K.byHyp 4)) <|
          K.impE (linkK K "cataClause: the remaining variables' flags" (K.byHyp 5)) <|
          K.impE (linkK K "cataClause: the body" (K.byHyp 6)) <|
          K.impE (linkK K "cataClause: the abbreviations" (K.byHyp 7)) <|
          K.impE (linkK K "cataClause: the names" (K.byHyp 8)) <|
          K.allEΓ fts <| K.allEΓ ts <| K.allEΓ rs <| K.allEΓ (wk first) <| K.allEΓ Ar <|
          K.allEΓ (fun _ ↦ numeral 1) <| K.allEΓ envW <| K.allEΓ cxW <| K.allEΓ kcW <|
          K.impE (linkK K "cataClause: the walk's typing" (byStep hTy)) <|
          K.impE (linkK K "cataClause: the constructor's test" (K.byHyp hOk)) <|
          K.impE (linkK K "cataClause: the lengths" (K.byHyp hLen)) <|
          K.impE (linkK K "cataClause: the results related" (K.byHyp hRel)) <|
          K.impE (linkK K "cataClause: the split's index" lookupOk) <|
          K.impE (linkK K "cataClause: the split's value" lookupOk) <|
          K.impE (linkK K "cataClause: the split's type" lookupOk) <|
          K.impE (linkK K "cataClause: the extended environment" envOk) <|
          K.impE (linkK K "cataClause: the extended context's names" cxOk) <|
          K.impE (linkK K "cataClause: the walk resolved" solved) <|
          K.impE (linkK K "cataClause: the walk's kernel typing" (K.byHyp iTr)) <|
          linkK K "cataClause: the walk's conclusion" fun Γ Φ ψ ↦ byStep (Φ.length - 1) Γ Φ ψ
      applyThm K "letTyped" (fun _ ↦ [e, rB, B, kc, g]) [K.byHyp hKer] (K.conjE fun Γ Φ ψ ↦
        let iT₁ := Φ.length - 2
        applyThm K "letTyped" (fun Γ ↦ [wk e₂ Γ, wk rB₂ Γ, wk B₂ Γ,
            consT treeTy (wk B Γ) (wk kc Γ), wk g Γ]) [K.byHyp iT₁] (K.conjE fun Γ Φ ψ ↦
          let iT₂ := Φ.length - 2
          applyThm K "letConv" (fun Γ ↦ [wk env Γ, wk e Γ, wk rB Γ, wk B Γ, isQ (wk val) Γ,
              wk Pg Γ, wk Rt Γ])
            [linkK K "cataClause: the pair's value" <| K.cutThm "clausePairConv" σp byLast,
              linkK K "cataClause: the children's binding" <| dAllI L <| dImpI L <| normLastK K <|
                applyThm K "letConv" (fun Γ ↦ [consT treeTy (wk val Γ) (wk env Γ), wk e₂ Γ,
                    wk rB₂ Γ, wk B₂ Γ, isQ qY Γ, wk Pg Γ, wk Rt Γ])
                  [linkK K "cataClause: the children's value" <|
                    K.cutThm "clauseChildrenConv" (fun Γ ↦ [env0 Γ, t Γ, kvT Γ, u Γ, wk val Γ,
                      R Γ]) byLast,
                    linkK K "cataClause: the rest's binding" <| dAllI L <| dImpI L <|
                      normLastK K (walkAt iT₂)] byLast]
            byLast Γ Φ ψ) Γ Φ ψ) Γ₀ Φ ψ
    let intros (k : Deducer) : Deducer :=
      (List.range 9).foldr (fun _ k ↦ dImpI L k) <|
        (List.range 6).foldr (fun _ k ↦ dAllI L k) <| (List.range 10).foldr (fun _ k ↦ dImpI L k) k
    let table : List (Term × String) := clauseExcluded P ++ cataExcluded P
    let some d := intros (plainAtoms K T (walkAtoms P ++ [childrenName P]) nums 1
        (excludedAtoms K T table nums 1 <| closedEqs <| letEqs <| decisions present)
        (lemmas := [(childrenName P, "childrenExcluded")]))
        a.ctx a.hyps a.concl
      | dbgTrace "cataClause: not proved" fun _ ↦ none
    pure (a, d))

/-- The decisions of the typing's walk's entry ({lit}`Typing.cataFields`), of position {lit}`e`, at
the raw field type {lit}`raw`, in the positions of {name}`cataWalkCtx` shifted by the walk's
variables: the entry's flag's test, the field's being the datatype's and, not, the field's type's
presence, and the entry's variable's being a clause's, each false by {lit}`absent`, at last
{lit}`k`. -/
def walkEntry (K : Kit) (e raw : List Tree → Term) (absent : String → Deducer) (k : Deducer) :
    Deducer :=
  let P := K.P
  let equalT := (primT Kernel.Prim.equal).getD Term.star
  let E' := atPos 9
  let es (Γ : List Tree) : Term := pc P "Typing.elemsTx" [e Γ]
  let atE (i : ℕ) (Γ : List Tree) : Term :=
    pc P "Typing/Txs.atOr" [pc P "Typing.tx0" [], es Γ, leafT (numeral i)]
  let isRec (Γ : List Tree) : Term := apps equalT [raw Γ, atPos 3 Γ]
  let f (Γ : List Tree) : Term := pc P "Typing.numTx" [atE 1 Γ]
  let test (Γ : List Tree) : Term := pc P "Prelude.and" [pc P "Prelude.isSome" [f Γ],
    eqL (pc P "Prelude.get" [f Γ]) (isRec Γ)]
  let var : Deducer :=
    decideIn K (fun Γ ↦ pc P "Typing.binderName" [E' Γ, atE 0 Γ]) (absent "not admitted") <|
    decideIn K (fun Γ ↦ pc P "Typing.clauseVar" [E' Γ, atE 0 Γ]) (absent "not a clause's") k
  decideIn K test (absent "the flag") <|
  decideIn K isRec
    (decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Typing.fieldTy" [E' Γ, raw Γ]])
      (absent "no type") var)
    var

/-- The walk of a structural recursion's clause's fields ({name}`cataWalkParts`) with a body's
typing absent at every named context is absent, at all field types and named contexts: by induction
on the fixed fields' entries, as {name}`caseFieldsNothing`. In {name}`cataWalkCtx`. -/
def cataFieldsNothing (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cataFieldsNothing", fun ix E ↦ do
    let P := cataVarProg P
    let w ← cataWalkParts ⟨P, S, E, ix, []⟩ T
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let o := P.o
    let steps : List Internal.NormRule :=
      ["Typing.bindRest", "Typing.bindVar", "Reader.numeral"].map fun nm ↦ .delta (P.idx nm)
    let byU : Deducer := fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ steps) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let constNothing := Term.lam (list treeTy) (nothingT P)
    let tyN := Term.subst w.ty fun i ↦ if i = 2 then constNothing else v i
    -- under the two quantifiers: the named context v0, the field types v1
    let φ := Internal.Logic.all o (list treeTy) (Term.lam (list treeTy)
      (Internal.Logic.all o (list treeTy) (Term.lam (list treeTy)
        (Term.eq (Term.app (Term.app (sh 2 tyN) (v 1)) (v 0)) (nothingT P)))))
    let childT ← primT Kernel.Prim.child
    let absent (msg : String) : Deducer := linkK K s!"cataFieldsNothing: {msg}" byU
    -- positions after the quantifiers: the default's form 0 to the body's erasure 13, then the
    -- field types 14 and the named context 15
    let c := atPos 10
    let nilCase : Deducer := dAllI L <| dAllI L fun Γ Φ ψ ↦
      K.listCase treeTy (atPos 14 Γ)
        (decideIn K (fun Γ ↦ apps childT [c Γ, leafT (numeral 2)])
          (K.listCase treeTy (atPos 11 Γ) byU byU)
          (fun Γ Φ ψ ↦ K.listCase treeTy (atPos 11 Γ) byU (fun Γ Φ ψ ↦
            let (r, more) := (atPos (Γ.length - 2), atPos (Γ.length - 1))
            K.listCase treeTy (more Γ)
              (walkEntry K r (fun Γ ↦ apps childT [c Γ, leafT (numeral 3)]) absent byU) byU Γ Φ ψ)
            Γ Φ ψ))
        byU Γ Φ ψ
    let r₀ := linkK K "cataFieldsNothing: no fields" nilCase (cataWalkCtx T).tail []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a fixed field: the entry 14, the rest 15, the field types 16 and the named context 17
    let consCase : Deducer := dAllI L <| dAllI L fun Γ Φ ψ ↦
      K.listCase treeTy (atPos 16 Γ) byU (fun Γ Φ ψ ↦
        let (ft, rest) := (atPos (Γ.length - 2), atPos (Γ.length - 1))
        walkEntry K (atPos 14) ft absent (fun Γ Φ ψ ↦
          match evalRw K.G K.E (K.rules Φ ++ steps) .full Γ Φ ψ with
          | none => none
          | some (g, _) =>
            let restT := rest Γ
            let found := RoseTree.para (fun l (cs : List (Term × Option Term)) ↦
              match cs.findSome? (·.2) with
              | some r => some r
              | none =>
                let u : Term := RoseTree.node l (cs.map Prod.fst)
                match u.label, u.children with
                | .app, [f, x] => match f.label, f.children with
                  | .app, [_, y] => if y == restT then some x else none
                  | _, _ => none
                | _, _ => none) g
            match found with
            | none => dbgTrace "cataFieldsNothing: no context" fun _ ↦ none
            | some cx' =>
              dAllE L K.G K.E 0 restT (K.allEΓ (fun _ ↦ cx') <| (fun k Γ Φ ψ ↦
                dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1) ++ steps) .full)
                  (Φ.length - 1) k Γ Φ ψ) <|
                linkK K "cataFieldsNothing: the rest" byU) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let r₁ := linkK K "cataFieldsNothing: a field" consCase
      (list treeTy :: treeTy :: (cataWalkCtx T).tail) [Internal.weakenElem φ]
      (Internal.listConsAt 1 treeTy φ)
    let some d₀ := r₀ | dbgTrace "cataFieldsNothing: the base not proved" fun _ ↦ none
    let some d₁ := r₁ | dbgTrace "cataFieldsNothing: the construction not proved" fun _ ↦ none
    pure (⟨0, cataWalkCtx T, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- An entry's variable admitted as a binder by the typing, as a predicate of an entry, at the
typing environment {lit}`E` outside its binder. -/
def binderEntry (P : Prog) (E : Term) : Term :=
  Term.lam treeTy (truth P.o (pc P "Typing.binderName" [sh 1 E, entryVar P (v 0)]))

/-- The walk of a structural recursion's clause's fields ({name}`cataWalkParts`), present at some
field types and named context, admits each entry's variable as a binder: by induction on the fixed
fields' entries, as {name}`walkBinders`. In {name}`cataWalkCtx`. -/
def cataWalkBinders (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cataWalkBinders", fun ix E ↦ do
    let P := cataVarProg P
    let w ← cataWalkParts ⟨P, S, E, ix, []⟩ T
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let o := P.o
    let steps : List Internal.NormRule :=
      ["Typing.bindRest", "Typing.bindVar", "Reader.numeral"].map fun nm ↦ .delta (P.idx nm)
    let childT ← primT Kernel.Prim.child
    -- under the two quantifiers: the named context v0, the field types v1
    let φ := Internal.Logic.all o (list treeTy) (Term.lam (list treeTy)
      (Internal.Logic.all o (list treeTy) (Term.lam (list treeTy) (Internal.Logic.imp o
        (truth o (pc P "Prelude.isSome" [Term.app (Term.app (sh 2 w.ty) (v 1)) (v 0)]))
        (Internal.Logic.conj o (S.allL (binderEntry P (v 7)) (v 2))
          (S.allL (binderEntry P (v 7)) (v 5)))))))
    let absentAt (h : ℕ) (msg : String) : Deducer := linkK K s!"cataWalkBinders: {msg}"
      fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ steps) .full) h (dFalse L dHyp) Γ Φ ψ
    let c := atPos 10
    let splitAt (p : ℕ) (k₀ k₁ : Deducer) : Deducer := fun Γ Φ ψ ↦
      K.listCase treeTy (atPos p Γ) k₀ k₁ Γ Φ ψ
    let nilCase : Deducer := dAllI L <| dAllI L <| dImpI L <|
      splitAt 14
        (decideIn K (fun Γ ↦ apps childT [c Γ, leafT (numeral 2)])
          (splitAt 11 (linkK K "cataWalkBinders: no rest" (K.solve 3))
            (absentAt 2 "a remaining variable without its field"))
          (splitAt 11 (absentAt 2 "no remaining variable") (fun Γ Φ ψ ↦
            let (pr, pm) := (Γ.length - 2, Γ.length - 1)
            splitAt pm
              (walkEntry K (atPos pr) (fun Γ ↦ apps childT [c Γ, leafT (numeral 3)]) (absentAt 2)
                (linkK K "cataWalkBinders: the remaining variable" (K.solve 3)))
              (absentAt 2 "two remaining variables") Γ Φ ψ)))
        (absentAt 2 "a field type without a variable")
    let r₀ := linkK K "cataWalkBinders: no fields" nilCase (cataWalkCtx T).tail []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let consCase : Deducer := dAllI L <| dAllI L <| dImpI L fun Γ Φ ψ ↦
      K.listCase treeTy (atPos 16 Γ) (absentAt 3 "a variable without a field type") (fun Γ Φ ψ ↦
        let (pf, pr) := (Γ.length - 2, Γ.length - 1)
        let (ft, rest) := (atPos pf, atPos pr)
        walkEntry K (atPos 14) ft (absentAt 3) (fun Γ Φ ψ ↦
          match (Φ[3]?).bind fun h ↦ evalRw K.G K.E (K.rulesEx Φ 3 ++ steps) .full Γ Φ h with
          | none => none
          | some (g, _) =>
            let restT := rest Γ
            let found := RoseTree.para (fun l (cs : List (Term × Option Term)) ↦
              match cs.findSome? (·.2) with
              | some r => some r
              | none =>
                let u : Term := RoseTree.node l (cs.map Prod.fst)
                match u.label, u.children with
                | .app, [f, x] => match f.label, f.children with
                  | .app, [_, y] => if y == restT then some x else none
                  | _, _ => none
                | _, _ => none) g
            match found with
            | none => dbgTrace "cataWalkBinders: no context" fun _ ↦ none
            | some cx' =>
              dAllE L K.G K.E 0 restT (K.allEΓ (fun _ ↦ cx') <|
                K.impE (linkK K "cataWalkBinders: the rest present" fun Γ Φ ψ ↦
                  dRwHyp (evalRw K.G K.E (K.rulesEx Φ 3 ++ steps) .full) 3
                    (dRwBy (evalRw K.G K.E (K.rules Φ ++ steps) .full) dHyp) Γ Φ ψ) <|
                K.conjE <| linkK K "cataWalkBinders: the variables" fun Γ Φ ψ ↦
                  let (iVs, iRvs) := (Φ.length - 2, Φ.length - 1)
                  K.norm (dConjI L (dConjI L (K.solve 3) (K.byHyp iVs)) (K.byHyp iRvs)) Γ Φ ψ)
                Γ Φ ψ) Γ Φ ψ)
        Γ Φ ψ
    let r₁ := linkK K "cataWalkBinders: a field" consCase
      (list treeTy :: treeTy :: (cataWalkCtx T).tail) [Internal.weakenElem φ]
      (Internal.listConsAt 1 treeTy φ)
    let some d₀ := r₀ | dbgTrace "cataWalkBinders: the base not proved" fun _ ↦ none
    let some d₁ := r₁ | dbgTrace "cataWalkBinders: the construction not proved" fun _ ↦ none
    pure (⟨0, cataWalkCtx T, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The development of a structural recursion's clauses. -/
def cataClausesDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  (clauseExcluded P).map (fun (n, nm) ↦ atomExcluded P S nm n) ++ clauseNums P S T ++
    [cataResAt "cataClauseRes" .present P S T, cataResAt "cataClauseNoType" .noType P S T,
      cataResAt "cataClauseNoDefault" .noDefault P S T, cataResAt "cataClauseNoRest" .noRest P S T,
      nthThree P S 4, nthOne P S 5, clausePairConv P S, clauseChildrenConv P S, cataClause P S T,
      cataFieldsNothing P S T, cataWalkBinders P S T]

/-- The soundness at a structural recursion's clauses, after the structural recursion's walk. -/
def cataClausesCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := caseNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (caseDev P S T).map (·.1) ++ (clausesDev P S T).map (·.1) ++
    (caseSoundDev P S T).map (·.1) ++ (cataDev P S T).map (·.1)) "datatype-cata-clauses"
    (cataClausesDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
