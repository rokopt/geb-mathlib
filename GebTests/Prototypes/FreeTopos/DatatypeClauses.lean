/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeCase
public import GebTests.Prototypes.FreeTopos.DatatypeDecode
public meta import GebTests.Prototypes.FreeTopos.DatatypeCase -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at a case analysis's clauses

The soundness of the datatype language's stage-1 compiler at a case analysis's clauses: a
clause's binding of the children remaining to the scrutinee's children around the walk of its
fields ({name}`GebTests.Prototypes.FreeTopos.Datatypes.walk`).

## Main definitions

* {lit}`clausesCertificates` — the development, stored as the certificate
  {lit}`datatype-clauses`.

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

/-- The scrutinee's name, as the reader reads it. -/
def scrutineeName (P : Prog) : Term := atomNameT (pc P "Datatype.aS" [])

/-- The children primitive's name, as the reader reads it. -/
def childrenName (P : Prog) : Term := atomNameT (pc P "Datatype.aChildren" [])

/-- The erasure's binding of a clause's children remaining to the children of the scrutinee,
around a rest {lit}`r`. -/
def clauseStep (P : Prog) (r : Term) : Term :=
  let aC := pc P "Datatype.aC" []
  let aT := pc P "Datatype.aT" []
  pc P "Datatype.sLet" [aC, pc P "Datatype.sList" [aT],
    pc P "Datatype.sx2" [pc P "Datatype.aChildren" [], pc P "Datatype.aS" []], r]

/-- The resolution of a clause's binding of its children remaining, in the scope headed by the
scrutinee's name, where the children primitive's name is in neither the scope's tail nor the
definitions' names: in the context of the rest, the scope's tail, the type abbreviations and the
definitions' names, its left side in the normal form of the walk's rules, its right side the
normal form with the reader's case of bindings and steps unfolded, the rest's resolution, in the
scope extended by the children remaining's name, folded. Proved by deciding the tests, true
refuting their hypotheses, then by normalization. -/
def clauseRes (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("clauseRes", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let Γ := [treeTy, list treeTy, list treeTy, list treeTy]
    let lhs := pc P "Reader.resolve" [v 2, v 3, clauseStep P (v 0),
      consT treeTy (scrutineeName P) (v 1)]
    let tests := [pc P "Prelude.isSome" [pc P "Reader.indexOf" [childrenName P, v 1]],
      pc P "Prelude.isSome" [pc P "Reader.indexOf" [childrenName P, v 3]]]
    let fails ← tests.mapM fun t ↦ do
      let (X, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (call D.lab [] [t])
      pure (Term.eq X bnilT)
    -- the failures' equations past a first hypothesis, which supplies no rule
    let Φ := Term.star :: fails
    let Kw : Kit := { K with more := walkRules ix E }
    let (l, _) ← evalRw Kw.G Kw.E (Kw.rules []) .full Γ [] lhs
    let unfold := resolveRules P T ix E
    let (r, _) ← evalRw K.G K.E (K.rules Φ ++ unfold) .full Γ Φ lhs
    let a : Internal.Thm := ⟨0, Γ, tests.map (notTest P.o), Term.eq l r⟩
    let decisions : Deducer → Deducer := fun k ↦
      tests.zipIdx.foldr (fun (t, i) k ↦
        decideIn K (fun _ ↦ t) k (linkK K s!"clauseRes: test {i} true" fun Γ Φ ψ ↦
          dImpE K.L i (K.solve 3) (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)) k
    let some d := decisions (linkK K "clauseRes: the sides" fun Γ Φ ψ ↦
        dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold) Γ
          (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "clauseRes: not proved" fun _ ↦ none
    pure (a, d))

/-- The kernel's term of the children of the variable of index 0, read off the present
resolution on the right side of {name}`clauseRes`: the argument of the binding's application. -/
def childrenTerm (E : Array Internal.Entry) (ix : String → ℕ) : Option Term := do
  let some (Internal.Entry.language b) := E[ix "clauseRes"]? | none
  let (_, r) ← Internal.eqParts b.concl
  let apps := RoseTree.para (fun l (cs : List (Term × List Term)) ↦
      let below := cs.flatMap (·.2)
      match nodeKidsT (RoseTree.node l (cs.map Prod.fst)) with
      | some [f, e] => match nodeKidsT f with
        | some [_, _] => e :: below
        | _ => below
      | _ => below) r
  apps.head?

/-- The equations evaluating the kernel's primitives at their arguments, and those of
{name}`evalMore`. -/
def evalPrims : List String :=
  evalMore ++ (List.range 14).flatMap fun k ↦ apNames s!"apPrim{k}" (primArgs k)

/-- The kernel's term of the scrutinee's children ({name}`childrenTerm`), in an environment whose
first value is a tree's quotation, converges to the list value of the quotations of the tree's
children. In the context of the environment's rest, the tree and the relation's context. Proved at
the level 5, the evaluation by the primitives' equations ({name}`evalPrims`). -/
def childrenConv (P : Prog) (S : Defs) : Step :=
  ("childrenConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, evalPrims.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let chK ← childrenTerm E ix
    let Γ := [list treeTy, treeTy, Defs3.ctxTy]
    let env := consT treeTy (pc P "Eval.valQuote" [v 1]) (v 0)
    let value := treeList P (quotesT P (call D.children [] [v 1]))
    let a : Internal.Thm := ⟨0, Γ, [], S.conv (Term.lam nat (S.evN (Term.fst (v 3)) (v 0)
      (sh 1 env) chK)) (Term.lam treeTy (Term.eq (v 0) (sh 1 value)))⟩
    let lv : Term := (5 : ℕ).rec zeroN fun _ t ↦ succN t
    let some d := dConv K.L K.G K.E S lv value
        (linkK K "childrenConv stable" K.byNorm) (linkK K "childrenConv value" (K.norm K.byNorm))
        a.ctx a.hyps a.concl
      | dbgTrace "childrenConv: not proved" fun _ ↦ none
    pure (a, d))

/-- The atoms of a clause's erasure: the walk's ({name}`walkAtoms`), the scrutinee's name and the
children primitive's. -/
def clauseAtoms (P : Prog) : List Term :=
  walkAtoms P ++ [scrutineeName P, childrenName P]

/-- The erasure's application of the children primitive to the scrutinee. -/
def childrenOfS (P : Prog) : Term :=
  pc P "Datatype.sx2" [pc P "Datatype.aChildren" [], pc P "Datatype.aS" []]

/-- The expansion of the numeral abbreviations at the erasure's application of the children
primitive to the scrutinee ({name}`childrenOfS`), the clause's atoms not abbreviated, is the
application itself. In the context of the numeral abbreviations. -/
def childrenNums (P : Prog) (S : Defs) (T : Defs3) : Step :=
  builderEq "childrenNums" P S [list treeTy] ((clauseAtoms P).map fun a ↦
      pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [a, v 0]])
    (pc P "Reader.expandNums" [v 0, childrenOfS P]) (fun _ _ _ ↦ [.delta (T.argIdx 3)])
    (childrenOfS P)

/-- The list of trees of a clause's metadata at a position: the fixed fields' variables at 1, the
remaining children's at 2, as the erasure's bindings read them. -/
def metaAt (P : Prog) (md : Term) (i : ℕ) : Term :=
  pc P "Datatype.elems" [pc P "Datatype.nthTx" [pc P "Datatype.elems" [md], leafT (numeral i)]]

/-- The erasure's bindings of a clause's variables, of metadata {lit}`md`, around its body
{lit}`b`. -/
def clauseBinds (P : Prog) (md b : Term) : Term :=
  let aT := pc P "Datatype.aT" []
  let aC := pc P "Datatype.aC" []
  let sLet (x a e b : Term) : Term := pc P "Datatype.sLet" [x, a, e, b]
  let fb := Term.lam treeTy (Term.lam treeTy (sLet (v 1) aT (pc P "Datatype.sHeadOf" [aC])
    (sLet aC (pc P "Datatype.sList" [aT]) (pc P "Datatype.sTailOf" [aC]) (v 0))))
  let rb := Term.lam treeTy (Term.lam treeTy (sLet (v 1) (pc P "Datatype.sList" [aT]) aC (v 0)))
  pc P "Datatype.bindVars" [fb, rb, md, b]

/-- The erasure of a case analysis's clause of metadata {lit}`md` and body {lit}`b`: the binding
of the children remaining to the scrutinee's children around the bindings of the clause's
variables ({name}`clauseBinds`). -/
def clauseErasure (P : Prog) (md b : Term) : Term := clauseStep P (clauseBinds P md b)

/-- The named context's entry of the scrutinee, at the type of the trees. -/
def scrutineeEntry (P : Prog) : Term :=
  pc P "Typing.abbr" [pc P "Typing.boundName" [pc P "Typing.kwScrutinee" []],
    pc P "Typing.tyT" []]

/-- The context of a clause: the metadata v0, the body's erasure v1, its typing as a function of
the named context v2, the scrutinee's tree v3, the constructor v4, and, as in {name}`walkCtx`, the
typing environment v5, the kernel's globals' types v6, the type and numeral abbreviations v7 and
v8, the definitions' names v9 and the relation's context v10. -/
def clauseCtx (T : Defs3) : List Tree :=
  [treeTy, treeTy, exp (list treeTy) treeTy, treeTy, treeTy, T.envTy, list treeTy,
    list treeTy, list treeTy, list treeTy, Defs3.ctxTy]

/-- The walk's instance at a clause ({name}`walkCtx` at {name}`clauseCtx`): the fixed fields'
variables and the remaining children's those of the clause's metadata ({name}`metaAt`), the other
variables the clause's. -/
def walkInst (P : Prog) (at_ : ℕ → Term) : List Term :=
  [metaAt P (at_ 0) 1, at_ 1, at_ 2, metaAt P (at_ 0) 2] ++ (List.range 7).map (at_ <| · + 4)

/-- The statement of a case analysis's clause, at {name}`clauseCtx`: where the relation's markers
are the typing environment's, no numeral abbreviation names a keyword, the clause's variables'
characters are fixed by the expansion of the numeral abbreviations, and the body's erasure is sound
at its typing ({name}`bodyφ`), for all named contexts, environments and kernel's contexts beneath
the scrutinee's entry, if the clause's typing is present in the named context extended by the
scrutinee's entry, the constructor's test holds of the memberships of the scrutinee's children, the
environment extended by the scrutinee's quotation is related to that context, whose names are
admitted, the clause's erasure resolves in its scope, of a type in the kernel's context, and the
children primitive's name is neither in the context's scope nor a definition's, the resolution
converges to a value related at the clause's type. -/
def clauseφ (P : Prog) (S : Defs) (T : Defs3) (w : WalkParts) : Term :=
  let o := P.o
  let all (A : Tree) (t : Term) : Term := Internal.Logic.all o A (Term.lam A t)
  let imp := Internal.Logic.imp o
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let childT := (primT Kernel.Prim.child).getD Term.star
  -- beneath the three quantifiers: the named context v2, the environment v1 and the kernel's
  -- context v0; the clause's context's variables shifted by 3
  let q (i : ℕ) : Term := v (i + 3)
  let cx := consT treeTy (scrutineeEntry P) (v 2)
  let env := consT treeTy (pc P "Eval.valQuote" [q 3]) (v 1)
  let tyC := pc P "Typing.caseFields" [q 5, q 4, q 0, q 2, cx]
  let ms := pc P "Typing.envMs" [q 5]
  let mem := Term.lam treeTy (pc P "Typing.memberships" [sh 1 ms, v 0])
  let fts := call D.children [] [apps childT [q 4, leafT (numeral 1)]]
  let okC := Term.app (foldrAt (sh 3 w.ok) fts) (mapListsT mem (call D.children [] [q 3]))
  let kw := pc P "Reader.resolve" [q 7, q 9, pc P "Reader.expandNums" [q 8,
    clauseErasure P (q 0) (q 1)], scopeOf P (q 8) cx]
  let fixed : Term := fixedAtom P (v 8)
  let unindexed (t : Term) : Term :=
    notTest o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [childrenName P, t]])
  imp (Term.eq (Term.snd (v 10)) (pc P "Typing.envMs" [v 5])) <| imp (T.kwsT (v 8)) <|
    imp (S.allL fixed (metaAt P (v 0) 1)) <| imp (S.allL fixed (metaAt P (v 0) 2)) <|
    imp (bodyφ P S T 0 (v 1) (v 2)) <|
    all (list treeTy) <| all (list treeTy) <| all (list treeTy) <|
    imp (isSomeT tyC) <| imp (truth o okC) <| imp (T.envT (q 10) cx env) <|
    imp (T.cxT (q 5) cx) <| imp (isSomeT kw) <|
    imp (isSomeT (pc P "Check.typeIn" [q 6, v 0, get kw])) <|
    imp (unindexed (scopeOf P (q 8) (v 2))) <| imp (unindexed (q 9)) <|
    S.conv (Term.lam nat (S.evN (Term.fst (sh 1 (q 10))) (v 0) (sh 1 env) (sh 1 (get kw))))
      (T.relT (q 10) (get tyC))

/-- The soundness at a case analysis's clause ({name}`clauseφ`): the atoms' decisions and the
builders' expansions; the clause's resolution by {name}`clauseRes`, the rest's present, else the
resolution refuted; the kernel's typing of the binding split ({lit}`letTyped`), and its
convergence ({lit}`letConv`), the children's by {name}`childrenConv`, the rest's in the
environment extended by their value by the walk ({name}`walk`) at the clause
({name}`walkInst`). -/
def clause (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("clause", fun ix E ↦ do
    let P := { walkProg P with folded := (walkProg P).folded ++ ["Check.typeIn"] }
    let w ← walkParts ⟨P, S, E, ix, []⟩ T
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let a : Internal.Thm := ⟨0, clauseCtx T, [], clauseφ P S T w⟩
    let steps : List Internal.NormRule := ["Typing.bindRest", "Typing.bindVar"].map fun nm ↦
      .delta (P.idx nm)
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let byStep (h : ℕ) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ steps) .full) h
        (dRwBy (evalRw K.G K.E (K.rules Φ ++ steps) .full) dHyp) Γ Φ ψ
    let (hTy, hOk, hEnv, hCx, hRes, hKer, hNs, hNn) := (8, 9, 10, 11, 12, 13, 14, 15)
    let negated : Deducer := dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let (R, names, nums, tys, E', c, t, b, md) :=
      (atPos 0, atPos 1, atPos 2, atPos 3, atPos 5, atPos 6, atPos 7, atPos 9, atPos 10)
    let (inner, env0) := (atPos 11, atPos 12)
    let aC := pc P "Datatype.aC" []
    let aT := pc P "Datatype.aT" []
    let childT ← primT Kernel.Prim.child
    -- the closed builders' expansions, then the binding's, then the resolution's equation
    let closedEqs (k : Deducer) : Deducer :=
      ["aTNums", "aCNums", "listTNums"].foldr (fun nm k ↦
        applyThm K nm (fun Γ ↦ [nums Γ]) ((walkAtoms P).map fun _ ↦ negated) <|
          normLastK K k) <|
      applyThm K "childrenNums" (fun Γ ↦ [nums Γ]) ((clauseAtoms P).map fun _ ↦ negated) <|
        normLastK K k
    let bodyB (Γ : List Tree) : Term := clauseBinds P (md Γ) (b Γ)
    let restEx (Γ : List Tree) : Term := pc P "Reader.expandNums" [nums Γ, bodyB Γ]
    let letEq (k : Deducer) : Deducer :=
      applyThm K "letNums" (fun Γ ↦ [bodyB Γ, childrenOfS P, pc P "Datatype.sList" [aT], aC,
        nums Γ]) [negated] <| normLastK K k
    let resEq (k : Deducer) : Deducer :=
      applyThm K "clauseRes" (fun Γ ↦ [restEx Γ, scopeOf P (nums Γ) (inner Γ), tys Γ, names Γ])
        [K.byHyp hNs, K.byHyp hNn] <| normLastK K k
    let restRes (Γ : List Tree) : Term := pc P "Reader.resolve" [tys Γ, names Γ, restEx Γ,
      consT treeTy (fieldsName P) (consT treeTy (scrutineeName P)
        (scopeOf P (nums Γ) (inner Γ)))]
    let unresolved : Deducer := linkK K "clause: the rest unresolved" fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ hRes) .full) hRes
        (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    let present : Deducer := linkK K "clause: the rest resolved" fun Γ₀ Φ ψ ↦ do
      let (g, kc, x) ← apps3Of (P.idx "Check.typeIn") (← Φ[hKer]?)
      let (y, _) ← evalRw K.G K.E (K.rules Φ) .full Γ₀ Φ x
      let [f, e] ← nodeKidsT y | dbgTrace "clause: the term" fun _ ↦ none
      let [B, rB] ← nodeKidsT f | dbgTrace "clause: the abstraction" fun _ ↦ none
      let [Pg, F] := ψ.children | dbgTrace "clause: the goal" fun _ ↦ none
      let [body] := F.children | none
      let [f₁, _] := body.children | none
      let [fs, env] := f₁.children | none
      let [lvl] := fs.children | none
      let [_, dR] := lvl.children | none
      let [Rt] := dR.children | none
      let lower (u : Term) : Term := Term.subst u fun j ↦ v (j - 1)
      let (Rt, env) := (lower Rt, lower env)
      let wk (u : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) u
      let ts (Γ : List Tree) : Term := call D.children [] [t Γ]
      let fts (Γ : List Tree) : Term := call D.children [] [apps childT [c Γ, leafT (numeral 1)]]
      let qY (Γ : List Tree) : Term := treeList P (quotesT P (ts Γ))
      let isQ (q : List Tree → Term) (Γ : List Tree) : Term :=
        Term.lam treeTy (Term.eq (v 0) (sh 1 (q Γ)))
      let cxS (Γ : List Tree) : Term := consT treeTy (scrutineeEntry P) (inner Γ)
      let envS (Γ : List Tree) : Term := consT treeTy (pc P "Eval.valQuote" [t Γ]) (env0 Γ)
      let fieldsNm : Term := pc P "Typing.boundName" [pc P "Typing.kwFields" []]
      let relY : Deducer := K.cutThm "relOfListT" (fun Γ ↦ [quotesT P (ts Γ)]) <|
        K.allEΓ (fun _ ↦ leafT (numeral Kernel.Label.tyTree)) <| K.allEΓ R <|
        K.allEΓ (fun _ ↦ tyTreeT) <|
        K.impE (K.cutThm "quotesRel" (fun Γ ↦ [ts Γ]) (K.allEΓ R byLast)) byLast
      let envOk : Deducer := applyThm K "envTCons" (fun Γ ↦ [qY Γ, fieldsEntry P, envS Γ,
          cxS Γ, R Γ])
        [K.byHyp hEnv, linkK K "clause: the children related" relY] byLast
      let cxOk : Deducer := fun Γ Φ ψ ↦
        let cons : Deducer := applyThm K "cxTCons" (fun Γ ↦
            [pc P "Typing.tyList" [pc P "Typing.tyT" []], fieldsNm, E' Γ, cxS Γ])
          [linkK K "clause: the children's name admitted" (K.solve 3), K.byHyp hCx]
          (linkK K "clause: the children's entry" byLast)
        decideIn K (fun Γ ↦ pc P "Typing.nameOk" [E' Γ, fieldsNm]) cons cons Γ Φ ψ
      -- the walk at the clause, in the environment extended by the children's value
      let bodyAt (iTr : ℕ) : Deducer :=
        K.cutThm "walk" (fun Γ ↦ walkInst P fun i ↦ atPos (10 - i) Γ) <|
        -- the markers the hypothesis of index 0, a rule of the normalization, as written
        K.impE (linkK K "clause: the markers" fun Γ Φ ψ ↦
          (dHyp Γ Φ ψ).orElse fun _ ↦ K.byNorm Γ Φ ψ) <|
        K.impE (linkK K "clause: the keywords" (K.byHyp 1)) <|
        K.impE (linkK K "clause: the variables' characters" (K.byHyp 2)) <|
        K.impE (linkK K "clause: the remaining variables' characters" (K.byHyp 3)) <|
        K.impE (linkK K "clause: the body" (K.byHyp 4)) <|
        K.allEΓ fts <| K.allEΓ ts <| K.allEΓ envS <| K.allEΓ cxS <| K.allEΓ (wk kc) <|
        K.impE (linkK K "clause: the walk's typing" (byStep hTy)) <|
        K.impE (linkK K "clause: the constructor's test" (K.byHyp hOk)) <|
        K.impE (linkK K "clause: the extended environment" envOk) <|
        K.impE (linkK K "clause: the extended context's names" cxOk) <|
        K.impE (linkK K "clause: the walk resolved" (K.solve 3)) <|
        K.impE (linkK K "clause: the walk's kernel typing" (K.byHyp iTr)) <|
        linkK K "clause: the walk's conclusion" fun Γ Φ ψ ↦ byStep (Φ.length - 1) Γ Φ ψ
      (applyThm K "letTyped" (fun _ ↦ [e, rB, B, kc, g]) [K.byHyp hKer] <| K.conjE <|
        fun Γ Φ ψ ↦
        let iTr := Φ.length - 2
        applyThm K "letConv" (fun Γ ↦ [wk env Γ, wk e Γ, wk rB Γ, wk B Γ, isQ qY Γ,
            wk Pg Γ, wk Rt Γ])
          [linkK K "clause: the children's value" <|
            K.cutThm "childrenConv" (fun Γ ↦ [env0 Γ, t Γ, R Γ]) byLast,
            linkK K "clause: the rest's binding" <| dAllI L <| dImpI L <|
              normLastK K (bodyAt iTr)] byLast Γ Φ ψ) Γ₀ Φ ψ
    let intros (k : Deducer) : Deducer :=
      (List.range 5).foldr (fun _ k ↦ dImpI L k) <| (List.range 3).foldr (fun _ k ↦ dAllI L k) <|
        (List.range 8).foldr (fun _ k ↦ dImpI L k) k
    let some d := intros (plainAtoms K T (clauseAtoms P) nums 1 (closedEqs <| letEq <| resEq <|
        decideOpt K restRes unresolved present)
        (lemmas := [(scrutineeName P, "scrutExcluded"), (childrenName P, "childrenExcluded")]))
        a.ctx a.hyps a.concl
      | dbgTrace "clause: not proved" fun _ ↦ none
    pure (a, d))

/-- The statement of a conditional's convergence: where the condition converges to a tree's
quotation, and the branch the tree's label selects, the first where it is not empty, converges to
a value of which a predicate {lit}`Pr` holds, the conditional converges to such a value. In the
context of the environment, the condition, the branches, the predicate, the relation's context
and the tree. -/
def condConvThm (P : Prog) (S : Defs) : Internal.Thm :=
  let Pred := exp treeTy omega
  ⟨0, [list treeTy, treeTy, treeTy, treeTy, Pred, Defs3.ctxTy, treeTy],
    [S.conv (Term.lam nat (S.evN (Term.fst (v 6)) (v 0) (v 1) (v 2)))
        (Term.lam treeTy (Term.eq (v 0) (pc P "Eval.valQuote" [v 7]))),
      S.conv (Term.lam nat (S.evN (Term.fst (v 6)) (v 0) (v 1)
        (condT treeTy (call D.lab [] [v 7]) (v 3) (v 4)))) (v 4)],
    S.conv (Term.lam nat (S.evN (Term.fst (v 6)) (v 0) (v 1) (condK (v 2) (v 3) (v 4)))) (v 4)⟩

/-- A conditional converges ({name}`condConvThm`): the condition's convergence's threshold, value
and stability, its value the tree's quotation; the branch's; the tree's label decided, selecting
the branch; both thresholds shifted to their sum, a level above which the conditional evaluates to
the branch's value: the condition at the conditional's level, unquoted to the tree, whose label
selects the branch, evaluated at the same level. -/
def condConv (P : Prog) (S : Defs) : Step :=
  ("condConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let a := condConvThm P S
    let d? : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      -- the condition's value's equation normalized, a rule rewriting the value
      dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) 0 (K.exE <| K.exE <| K.conjE
        fun Γ₁ Φ₁ ψ₁ ↦
        let ne := atPos (Γ₁.length - 2)
        let se := Φ₁.length - 2
        normLastK K (fun Γ₁ Φ₁ ψ₁ ↦
        dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) 1 (K.exE <| K.exE <| K.conjE
          fun Γ₂ Φ₂ ψ₂ ↦
          let (nb, wb) := (atPos (Γ₂.length - 2), atPos (Γ₂.length - 1))
          let (sb, pb) := (Φ₂.length - 2, Φ₂.length - 1)
          let sum (Γ : List Tree) : Term := S.add (ne Γ) (nb Γ)
          -- a level above the sum, the stabilities at the successor of the conditional's offset
          let branch (msg : String) : Deducer := linkK K s!"condConv {msg}" <|
            shiftK K se false nb <| shiftK K sb true ne fun Γ Φ ψ ↦
              let (e₁, b₁) := (Φ.length - 2, Φ.length - 1)
              dConv L K.G K.E S (succN (sum Γ)) (wb Γ)
                (linkK K "condConv stable" <| instNK K e₁ (fun _ ↦ succN (v 0)) <|
                  instNK K b₁ (fun _ ↦ succN (v 0)) K.byNorm)
                (linkK K "condConv satisfied" (K.byHyp pb)) Γ Φ ψ
          match evalRw K.G K.E (K.rules Φ₂) .full Γ₂ Φ₂ (call D.lab [] [atPos 0 Γ₂]) with
          | some (Y, _) => K.listCase bitTy Y (branch "second") (branch "first") Γ₂ Φ₂ ψ₂
          | none => dbgTrace "condConv: no label" fun _ ↦ none) Γ₁ Φ₁ ψ₁) Γ₁ Φ₁ ψ₁)
        Γ₀ Φ₀ ψ₀
    let some d := d? a.ctx a.hyps a.concl | dbgTrace "condConv: not proved" fun _ ↦ none
    pure (a, d))

/-- The type of a typing's subterm's result: the subterm's form and its typing as a function of
the named context. -/
def srTy : Tree := prod treeTy (exp (list treeTy) treeTy)

/-- The program of the chain of a case analysis's clauses: the walk's, the constructors' tests,
the kernel's typing, the clause's fields' typing, a clause's type and the agreement of types kept
folded. -/
def chainProg (P : Prog) : Prog :=
  { caseProg (walkProg P) with folded := (caseProg (walkProg P)).folded ++
    ["Check.typeIn", "Typing.caseFields", "Typing.clauseTy", "Typing.sameAll"] }

/-- The equations of comparisons of lengths at constructions. -/
def lenRules : List String :=
  ["cmpSuccP", "addOne", "ltZero", "ltZeroSucc", "lenK", "ltSucc1"]

/-- The typing of a clause's fields, as a function of the constructor, the metadata, the body's
typing and the named context, at the typing environment {lit}`E` outside the four binders. -/
def caseFieldsFn (P : Prog) (E : Term) : Term :=
  Term.lam treeTy (Term.lam treeTy (Term.lam (exp (list treeTy) treeTy)
    (Term.lam (list treeTy) (pc P "Typing.caseFields" [sh 4 E, v 3, v 2, v 1, v 0]))))

/-- The scrutinee's entry alone, which a case analysis's typing binds around its clauses. -/
def scrutineeBase (P : Prog) : Term := consT treeTy (scrutineeEntry P) (nilT treeTy)

/-- The list of the types of a case analysis's clauses, and of its else clause's body where it has
one, at the constructors, the metadata, the bodies' typings, the named context and the typing
environment: the argument of the agreement of types in the normal form of the clauses' typing
({lit}`Typing.clausesTy`), in the context {lit}`Γ`. -/
def chainTysWith (base fields : Term) (K : Kit) (Γ : List Tree) (specs mds srs cx : Term) :
    Option Term := do
  let P := K.P
  let (z, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (pc P "Typing.clausesTy"
    [specs, mds, srs, cx, base, fields])
  let a ← (appsOf K.G (P.idx "Typing.sameAll") z).head?
  (spineArgs a).getLast?

/-- The list of the types of a case analysis's clauses ({name}`chainTysWith`). -/
def chainTys (K : Kit) (Γ : List Tree) (specs mds srs cx E : Term) : Option Term :=
  chainTysWith (scrutineeBase K.P) (caseFieldsFn K.P E) K Γ specs mds srs cx

/-- The erasure's binding of a clause's variables around its body, as a function of the metadata
and the body. -/
def bindFn (P : Prog) : Term :=
  Term.lam treeTy (Term.lam treeTy (clauseErasure P (v 1) (v 0)))

/-- A tree's characters fixed by the expansion of the numeral abbreviations {lit}`nums` where it
is an atom ({name}`fixedAtom`). -/
def fixedT (P : Prog) (nums : Term) : Term := fixedAtom P nums

/-- The label's atom of a clause's metadata. -/
def labelAtom (P : Prog) (md : Term) : Term :=
  pc P "Datatype.nthTx" [pc P "Datatype.elems" [md], leafT bnilT]

/-- The label a case analysis's typing reads off a clause's metadata: the numeral of its label's
atom, else 0. -/
def labelOf (P : Prog) (md : Term) : Term :=
  let j := pc P "Typing.numTx" [pc P "Typing/Txs.atOr" [pc P "Typing.tx0" [],
    pc P "Typing.elemsTx" [md], leafT bnilT]]
  condT treeTy (call D.lab [] [pc P "Prelude.isSome" [j]]) (pc P "Prelude.get" [j])
    (leafT bnilT)

/-- The labels of a list of clauses' metadata ({name}`labelOf`), by the prelude's right fold. -/
def labelsT (P : Prog) (mds : Term) : Term :=
  foldrT treeTy (list treeTy) (Term.lam treeTy (Term.lam (list treeTy)
    (consT treeTy (labelOf P (v 1)) (v 0)))) (nilT treeTy) mds

/-- A tree's label, as a tree. -/
def labT (t : Term) : Term := leafT (call D.lab [] [t])

/-- The memberships of a tree's children in the markers' datatypes, at the markers {lit}`ms`. -/
def childMemberships (P : Prog) (ms t : Term) : Term :=
  mapListsT (Term.lam treeTy (pc P "Typing.memberships" [sh 1 ms, v 0]))
    (call D.children [] [t])

/-- The comparison of two lengths, the kernel's primitive applied. -/
def ltL (a b : Term) : Term := apps ((primT Kernel.Prim.lt).getD Term.star) [a, b]

/-- The erasure's test of the label of the tree of the atom {lit}`sv`'s equality to a clause's
label, an atom of the characters {lit}`cs`. -/
def testAt (P : Prog) (sv cs : Term) : Term :=
  pc P "Datatype.sx3" [pc P "Datatype.aEq" [], pc P "Datatype.sx2" [pc P "Datatype.aLabel" [], sv],
    nodeT (Term.pair (numeral 1) cs)]

/-- The erasure's test of the scrutinee's label's equality to a clause's label ({name}`testAt`). -/
def testT (P : Prog) (cs : Term) : Term := testAt P (pc P "Datatype.aS" []) cs

/-- What the erasure's test of a chain of clauses depends on: the tested tree's atom and name, the
scope around the tested tree's name, and the names of the test's lemmas. -/
structure TestSpec where
  /-- The tested tree's atom. -/
  sv : Term
  /-- The tested tree's name, as the reader reads it. -/
  svName : Term
  /-- The reader's scope of the clauses, before a scope. -/
  scope : Term → Term
  /-- The name of the lemma of the tested tree's index in that scope. -/
  index : String
  /-- The names of the lemmas that the atoms of the test are no numerals, with those atoms. -/
  atoms : List (String × Term)
  /-- The name of the test's resolution. -/
  res : String
  /-- The name of the test's expansion. -/
  nums : String
  /-- The name of the test's convergence. -/
  conv : String
  /-- The environment of the test's convergence around the tested tree and the environment's
  rest, in that lemma's context: its rest v0, the tree v1, the relation's context v2, the characters
  v3 and the further variables {lit}`envCtx` from v4. -/
  env : Term → Term → Term
  /-- The further variables of the environment. -/
  envCtx : List Tree
  /-- The equations of the lookups of the test's convergence. -/
  lookups : List String

/-- The names of the primitives the erasure's test applies, as the reader reads them. -/
def testPrims (P : Prog) : List Term :=
  [atomNameT (pc P "Datatype.aEq" []), atomNameT (pc P "Datatype.aLabel" [])]

/-- The atoms of the erasure's test written by the erasure itself, with the names of their lemmas
that they are no numerals. -/
def testAtoms (P : Prog) : List (String × Term) :=
  [("aEqNotNumeral", pc P "Datatype.aEq" []), ("aLabelNotNumeral", pc P "Datatype.aLabel" []),
    ("aSNotNumeral", pc P "Datatype.aS" [])]

/-- An atom's characters, read by the reader's reading of numerals, are no numeral: the test of the
reading's presence, in the normal form with the reading kept folded, is empty. Closed; proved by
normalization with the reading unfolded. -/
def notNumeral (P : Prog) (S : Defs) (name : String) (atom : Term) : Step :=
  (name, fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let t := call D.lab [] [pc P "Prelude.isSome" [pc P "Reader.numeral"
      [call D.children [] [atom]]]]
    let (l, _) ← evalRw K.G K.E (K.rules []) .full [] [] t
    let a : Internal.Thm := ⟨0, [], [], Term.eq l bnilT⟩
    let some d := byMode .full K.G K.E 0 (K.rules [] ++ [.delta (P.idx "Reader.numeral")]) [] []
        l bnilT
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The rules of the vocabulary of the erasure's test: the walk's, the equation of the reader's
index at a construction replaced by that of its presence, which does not duplicate the rest's
index, so that the index of a name not fixed among fixed names stays a disjunction of tests. -/
def testMore (ix : String → ℕ) (E : Array Internal.Entry) : List String :=
  (walkMore ix E).filter (· ≠ "indexOfCons") ++
    (["isSomeIndexOfCons"].filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size)

/-- The index of a fixed name among names, the name at a position of the list's cells: the index's
equation at each suffix of the list, from the name's cell outward, each by the lookup's equation at
a construction ({lit}`indexOfCons`) under the equation after it, the reader's index kept folded
({name}`testMore`), so that no step unfolds the index at the rest. -/
def indexLemma (P : Prog) (S : Defs) (name : String) (Γ : List Tree) (x xs : Term) : Step :=
  (name, fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, testMore ix E⟩
    let nf (t : Term) : Option Term := (evalRw K.G K.E (K.rules []) .full Γ [] t).map Prod.fst
    let ns ← nf xs
    let xN ← nf x
    let cells := consCells ns
    let some p := cells.findIdx? (·.1 == xN) | dbgTrace s!"{name}: not found" fun _ ↦ none
    let suffix (l : ℕ) : Term := if l = 0 then ns else ((cells[l - 1]?).map Prod.snd).getD ns
    let headAt (l : ℕ) : Term := ((cells[l]?).map Prod.fst).getD Term.star
    let val (i : ℕ) : Term := pc P "Prelude.some" [leafT (numeral (p - i))]
    let (l, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (pc P "Reader.indexOf" [x, xs])
    let (r, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (val 0)
    let a : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let chain : Deducer := (List.range (p + 1)).reverse.foldr (fun i k Γ Φ ψ ↦ do
        let φ := Term.eq (pc P "Reader.indexOf" [xN, suffix i]) (val i)
        let d ← linkK K s!"{name}: at {i}" (K.cutThm "indexOfCons"
          (fun _ ↦ [suffix (i + 1), headAt i, xN]) K.byNorm) Γ Φ φ
        dCut φ d k Γ Φ ψ) (linkK K s!"{name}: the sides" K.byNorm)
    -- truth cut in first: the hypothesis of index 0 supplies no rule
    let some d := dCut (Internal.Logic.tt P.o) Internal.Logic.trueI chain a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- What the case analysis's test depends on: the scrutinee at the head of the scope. -/
def caseTest (P : Prog) : TestSpec where
  sv := pc P "Datatype.aS" []
  svName := scrutineeName P
  scope := consT treeTy (scrutineeName P)
  index := "aSIndexHead"
  atoms := testAtoms P
  res := "testRes"
  nums := "testNums"
  conv := "testConv"
  env := fun t e ↦ consT treeTy (pc P "Eval.valQuote" [t]) e
  envCtx := []
  lookups := []

/-- The indices of the erasure test's names: the scrutinee's at the head of a scope, of the scope's
tail, and the primitives' among the primitives' names. -/
def indexLemmas (P : Prog) (S : Defs) : List Step :=
  [indexLemma P S "aSIndexHead" [list treeTy] (scrutineeName P)
      (consT treeTy (scrutineeName P) (v 0))] ++
    ((testPrims P).zip ["aEqPrimIndex", "aLabelPrimIndex"]).map fun (n, nm) ↦
      indexLemma P S nm [] n (pc P "Reader.primNames" [])

/-- The resolution of the erasure's test ({name}`testAt`) in the scope of the tested tree's name,
the label's characters a numeral and the primitives' names in neither the scope nor the
definitions' names: in the context of the characters, the scope's tail, the type abbreviations
and the definitions' names, its right side the normal form with the reader's steps unfolded.
Proved by deciding the tests, each against its hypothesis, then by normalization. -/
def testResAt (t : TestSpec) (P : Prog) (S : Defs) (T : Defs3) : Step :=
  (t.res, fun ix E ↦ do
    let P := walkProg P
    -- the reader's index kept folded, the closed indices by their lemmas
    let K : Kit := ⟨P, S, E, ix, (walkMore ix E).filter (· ≠ "indexOfCons") ++
      [t.index, "aEqPrimIndex", "aLabelPrimIndex"]⟩
    let Γ := [list treeTy, list treeTy, list treeTy, list treeTy]
    let sc := t.scope (v 1)
    let lhs := pc P "Reader.resolve" [v 2, v 3, testAt P t.sv (v 0), sc]
    let numT := pc P "Prelude.isSome" [pc P "Reader.numeral" [v 0]]
    let isIn (n xs : Term) : Term := pc P "Prelude.isSome" [pc P "Reader.indexOf" [n, xs]]
    -- the tests of the names' indices, at the scope and the names, as the resolution reads them
    let tests := (testPrims P).flatMap fun n ↦ [isIn n sc, isIn n (v 3)]
    let nfL (t : Term) : Option Term :=
      (evalRw K.G K.E (K.rules []) .full Γ [] (call D.lab [] [t])).map Prod.fst
    let one ← (evalRw K.G K.E (K.rules []) .full Γ [] (numeral 1)).map Prod.fst
    let numEq := Term.eq (← nfL numT) one
    let fails ← tests.mapM fun t ↦ do pure (Term.eq (← nfL t) bnilT)
    -- the equations past a first hypothesis, which supplies no rule
    let Φ := Term.star :: numEq :: fails
    -- the reader's steps unfolded but its reading of numerals and its index, the closed atoms'
    -- readings by their lemmas, the label's characters' reading present by the hypothesis
    let unfold : List Internal.NormRule :=
      [T.argIdx 4, P.idx "Reader.resolveList", P.idx "Reader.resolveAtom"].map .delta ++
      t.atoms.map fun (nm, _) ↦ .thm (ix nm) []
    let (r, _) ← evalRw K.G K.E (K.rules Φ ++ unfold) .full Γ Φ lhs
    let a : Internal.Thm := ⟨0, Γ, truth P.o numT :: tests.map (notTest P.o), Term.eq lhs r⟩
    let name := t.res
    let decisions : Deducer → Deducer := fun k ↦
      tests.zipIdx.foldr (fun (t, i) k ↦
        decideIn K (fun _ ↦ t) k (linkK K s!"{name}: test {i} true" fun Γ Φ ψ ↦
          dImpE K.L (i + 1) (K.solve 3)
            (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)) k
    -- the names' tests first, whose false cases add no variables, then the numeral's presence
    let some d := decisions (decideIn K (fun _ ↦ numT)
        (linkK K s!"{name}: no numeral" (K.hypFalse 0))
        (linkK K s!"{name}: the sides" fun Γ Φ ψ ↦
          dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold) Γ
            (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ)) a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    let _ ← if (Term.occurs r 1 || Term.occurs r 2 || Term.occurs r 3) then
        dbgTrace s!"{name}: the right side not closed" fun _ ↦ none
      else some ()
    pure (a, d))

/-- The resolution of the case analysis's test ({name}`testResAt`). -/
def testRes (P : Prog) (S : Defs) (T : Defs3) : Step := testResAt (caseTest P) P S T

/-- The erasure's conditional's equations: the expansion of the numeral abbreviations at a
conditional, its keyword not abbreviated, the conditional of the parts' expansions; the reader's
resolution at a conditional, the reader's arguments of the kernel's conditional
({lit}`Reader.mkArgs`) at the parts' resolutions, kept folded. -/
def ifEqs (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let en (nums t : Term) : Term := pc P "Reader.expandNums" [nums, t]
  let sIf (c a b : Term) : Term := pc P "Datatype.sIf" [c, a, b]
  let res : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule :=
    fun P ix E ↦ resolveRules P T ix E
  let step3 : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule :=
    fun _ _ _ ↦ [.delta (T.argIdx 3)]
  -- the parts v2, v1 and v0, then the scope v3, the type abbreviations v4 and the names v5
  let rv (t : Term) : Term := pc P "Reader.resolve" [v 4, v 5, t, v 3]
  let ifCaseT : Term := pc P "Reader.mkArgs" [leafT (numeral Kernel.Label.cond),
    pc P "Reader.allSome" [consT treeTy (rv (v 2)) (consT treeTy (rv (v 1))
      (consT treeTy (rv (v 0)) (nilT treeTy)))]]
  [builderEq "ifNums" P S [treeTy, treeTy, treeTy, list treeTy]
      [pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [pc P "Reader.kwIf" [], v 3]]]
      (en (v 3) (sIf (v 2) (v 1) (v 0))) step3 (sIf (en (v 3) (v 2)) (en (v 3) (v 1))
        (en (v 3) (v 0))),
    builderEq "ifRes" P S [treeTy, treeTy, treeTy, list treeTy, list treeTy, list treeTy] []
      (pc P "Reader.resolve" [v 4, v 5, sIf (v 2) (v 1) (v 0), v 3]) res ifCaseT]

/-- The expansion of the numeral abbreviations at the erasure's test ({name}`testAt`) is the test,
where the names of its atoms are not abbreviated and the label's characters are fixed by the
expansion: in the context of the characters and the numeral abbreviations; the tests decided, true
refuting their hypotheses, the characters' equation ({lit}`charsFixedEq`) cut in, then the sides by
normalization with the expansion unfolded. -/
def testNumsAt (t : TestSpec) (P : Prog) (S : Defs) (T : Defs3) : Step :=
  (t.nums, fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let Γ := [list treeTy, list treeTy]
    let en (t : Term) : Term := pc P "Reader.expandNums" [v 1, t]
    let names := testPrims P ++ [t.svName, nodeT (Term.pair (numeral 0) (v 0))]
    let tests := names.map fun n ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [n, v 1]]
    let fixed := truth P.o (pc P "charsFixed"
      [Term.lam treeTy (pc P "Reader.expandNums" [v 2, v 0]), v 0])
    let (l, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (en (testAt P t.sv (v 0)))
    let (r, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (testAt P t.sv (v 0))
    let a : Internal.Thm := ⟨0, Γ, tests.map (notTest P.o) ++ [fixed], Term.eq l r⟩
    let decisions : Deducer → Deducer := fun k ↦
      tests.zipIdx.foldr (fun (t, i) k ↦
        decideIn K (fun _ ↦ t) k (linkK K s!"testNums: test {i} true" fun Γ Φ ψ ↦
          dImpE K.L i (K.solve 3) (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)) k
    let some d := decisions (K.cutThm "charsFixedEq" (fun _ ↦ [v 0, v 1]) <|
        K.impE (linkK K "testNums: the characters" (K.byHyp tests.length)) <| normLastK K <|
        linkK K "testNums: the sides" fun Γ Φ ψ ↦
          dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ [.delta (T.argIdx 3)]) Γ
            (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "testNums: not proved" fun _ ↦ none
    pure (a, d))

/-- The expansion at the case analysis's test ({name}`testNumsAt`). -/
def testNums (P : Prog) (S : Defs) (T : Defs3) : Step := testNumsAt (caseTest P) P S T

/-- The kernel's term of the erasure's test at the characters of the variable of index {lit}`i`,
read off the right side of the resolution lemma {lit}`res`, its present value. -/
def testTermAt (res : String) (i : ℕ) (K : Kit) (Γ : List Tree) : Option Term := do
  let some (Internal.Entry.language b) := K.E[K.ix res]? | none
  let (_, r) ← Internal.eqParts b.concl
  let r' := Term.subst r fun j ↦ if j = 0 then v i else Term.star
  match evalRw K.G K.E (K.rules []) .full Γ [] (pc K.P "Prelude.get" [r']) with
  | some (t, _) => some t
  | none => dbgTrace s!"testTerm: no normal form" fun _ ↦ none

/-- The kernel's term of the erasure's test, read off the right side of the case analysis's test's
resolution ({name}`testTermAt`). -/
def testTerm (K : Kit) (Γ : List Tree) : Option Term := testTermAt "testRes" 3 K Γ

/-- The kernel's term of the erasure's test ({name}`testTermAt`), in the environment of the
specification, of the tested tree's quotation, converges to the quotation of the equality of the
tree's label and the numeral of the characters. In the context of the environment's rest, the tree,
the relation's context, the characters, then the environment's further variables. Proved at the
level 5, by the primitives' equations ({name}`evalPrims`). -/
def testConvAt (t : TestSpec) (P : Prog) (S : Defs) : Step :=
  (t.conv, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, (evalPrims ++ t.lookups).filter
      fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let Γ := [list treeTy, treeTy, Defs3.ctxTy, list treeTy] ++ t.envCtx
    let tK ← testTermAt t.res 3 K Γ
    let env := t.env (v 1) (v 0)
    let value := pc P "Eval.valQuote" [eqL (labT (v 1))
      (pc P "Prelude.get" [pc P "Reader.numeral" [v 3]])]
    let a : Internal.Thm := ⟨0, Γ, [], S.conv (Term.lam nat (S.evN (Term.fst (v 3)) (v 0)
      (sh 1 env) (sh 1 tK))) (Term.lam treeTy (Term.eq (v 0) (sh 1 value)))⟩
    let lv : Term := (5 : ℕ).rec zeroN fun _ t ↦ succN t
    let some d := dConv K.L K.G K.E S lv value
        (linkK K s!"{t.conv} stable" K.byNorm) (linkK K s!"{t.conv} value" (K.norm K.byNorm))
        a.ctx a.hyps a.concl
      | dbgTrace s!"{t.conv}: not proved" fun _ ↦ none
    pure (a, d))

/-- The convergence of the case analysis's test ({name}`testConvAt`). -/
def testConv (P : Prog) (S : Defs) : Step := testConvAt (caseTest P) P S

/-- The statement of the kernel's typing of a conditional at its branches: where the kernel types
the conditional, it types each branch. In the context of the condition, the branches, the kernel's
context and the globals' types. -/
def condTypedThm (P : Prog) : Internal.Thm :=
  let typed (ctx t : Term) : Term :=
    truth P.o (pc P "Prelude.isSome" [pc P "Check.typeIn" [v 4, ctx, t]])
  ⟨0, [treeTy, treeTy, treeTy, list treeTy, list treeTy],
    [typed (v 3) (condK (v 0) (v 1) (v 2))],
    Internal.Logic.conj P.o (typed (v 3) (v 1)) (typed (v 3) (v 2))⟩

/-- The kernel's typing of a conditional at its branches ({name}`condTypedThm`): the condition's
and the branches' types decided, each absent refuting the hypothesis; the conjuncts then by
normalization. -/
def condTyped (P : Prog) (S : Defs) : Step :=
  ("condTyped", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let a := condTypedThm P
    let (c, x, y, C, G) := (atPos 4, atPos 3, atPos 2, atPos 1, atPos 0)
    let refute (msg : String) : Deducer := linkK K s!"condTyped: {msg}" (K.hypFalse 0)
    let typeIn (t : List Tree → Term) (Γ : List Tree) : Term := pc P "Check.typeIn" [G Γ, C Γ, t Γ]
    let some d := (decideOpt K (typeIn c) (refute "the condition untyped") <|
        decideOpt K (typeIn x) (refute "the first branch untyped") <|
        decideOpt K (typeIn y) (refute "the second branch untyped") <|
        linkK K "condTyped: the parts" (dConjI K.L (K.solve 3) (K.solve 3)))
        a.ctx a.hyps a.concl
      | dbgTrace "condTyped: not proved" fun _ ↦ none
    pure (a, d))

/-- What the chain of clauses of a case analysis or a structural recursion depends on. Each
function of a variable's term {lit}`ex` reads the clauses' common type at 0 and the specification's
further variables from 1, in the order of {lit}`extra`. -/
structure ChainSpec where
  /-- The lemma's name. -/
  name : String
  /-- The program of the proof. -/
  prog : Prog
  /-- The erasure's test. -/
  test : TestSpec
  /-- The specification's further variables, outside those of {lit}`chainCtx`. -/
  extra : List Tree
  /-- The named context the clauses are typed in, around a named context. -/
  cx : (ℕ → Term) → Term → Term
  /-- The environment of the clauses, around the scrutinee and an environment. -/
  env : (ℕ → Term) → Term → Term → Term
  /-- The named context's entries the typing binds around the clauses. -/
  base : (ℕ → Term) → Term
  /-- The clause's typing's fields' function ({lit}`Typing.clauseTy`), at the typing environment. -/
  fields : (ℕ → Term) → Term → Term
  /-- The erasure's binding of a clause, a function of the metadata and the body. -/
  bind : (ℕ → Term) → Term
  /-- The erasure of a clause, of metadata {lit}`md` and body {lit}`b`. -/
  erasure : (ℕ → Term) → Term → Term → Term
  /-- The predicate of the characters of the clause's variables' lists, at the abbreviations. -/
  fixedVar : Term → Term
  /-- The further conjuncts of a clause's metadata's hypothesis, at the metadata. -/
  metaExtra : Term → List Term
  /-- The further hypotheses of the chain, in the context beneath the bodies' and typings'
  quantifiers. -/
  extraHyps : (ℕ → Term) → List Term
  /-- The name of the clause's lemma. -/
  clauseAt : String
  /-- The name of the lemma that the walk at an absent body is absent. -/
  fieldsNothing : String
  /-- The name of the lemma of the clause's variables' being binders. -/
  walkBinders : String
  /-- The name of the lemma of the erasure of the clause's metadata. -/
  eraseMeta : String
  /-- The definition of the clause's fields' typing. -/
  fieldsDef : String
  /-- The definitions unfolded in the normal form of the walk ({lit}`fieldsNothing`) that the
  program keeps folded. -/
  walkDefs : List String
  /-- The named context of the walk around a named context, in the proof's context. -/
  cxWalk : (ℕ → Term) → Term → Term
  /-- The further arguments of {lit}`fieldsNothing` and {lit}`walkBinders`. -/
  walkExtra : (ℕ → Term) → List Term
  /-- The further arguments of the test's convergence. -/
  testExtra : (ℕ → Term) → List Term
  /-- The name of the lemma of the clause at its constructor. -/
  clause : String
  /-- The further arguments of {lit}`clause`. -/
  clauseArgs : (ℕ → Term) → List Term
  /-- The conjuncts of {lit}`metaExtra` {lit}`clause` takes, its first. -/
  clauseFlags : Term → List Term
  /-- The further hypotheses {lit}`clause` takes before its quantifiers, by their indices. -/
  preHyps : List ℕ
  /-- The instances of the further quantifiers of {lit}`clause`, after the three of the context. -/
  clauseAlls : (ℕ → Term) → List Term
  /-- The further hypotheses {lit}`clause` takes after the constructor's test, by their indices. -/
  midHyps : List ℕ
  /-- The name of the lemma that the tested tree's name is excluded from abbreviation. -/
  svExcluded : String
  /-- The further names of the clauses' scope, with their lemmas of that exclusion. -/
  scopeNames : List (Term × String)

/-- The context of a clause of the chain: the clause's metadata v0, its body's erasure v1,
its body's typing v2, the scrutinee's tree v3, the constructors v4, the typing environment v5, the
kernel's globals' types v6, the type and numeral abbreviations v7 and v8, the definitions' names
v9, the relation's context v10 and the clauses' common type v11. -/
def clauseAtCtx (T : Defs3) : List Tree :=
  [treeTy, treeTy, srTy, treeTy, list treeTy, T.envTy, list treeTy, list treeTy, list treeTy,
    list treeTy, Defs3.ctxTy, treeTy]

/-- The statement of a clause of the chain, at {name}`clauseAtCtx`: where the relation's markers
are the typing environment's, no numeral abbreviation names a keyword, the clause's variables'
characters are fixed, its body is sound at its typing and the scrutinee is of some constructor;
for all named contexts, environments and kernel's contexts beneath the scrutinee's entry, if the
clause's label is the scrutinee's, the clause's type is the common one, the environment extended
by the scrutinee's quotation is related to the named context extended by its entry, whose names
are admitted, the clause's erasure resolves, of a type in the kernel's context, and the children
primitive's name is neither in the context's scope nor a definition's, the resolution converges
to a value related at the common type. -/
def clauseAtφ (c : ChainSpec) (P : Prog) (S : Defs) (T : Defs3) : Term :=
  let o := P.o
  let all (A : Tree) (t : Term) : Term := Internal.Logic.all o A (Term.lam A t)
  let imp := Internal.Logic.imp o
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let ms := pc P "Typing.envMs" [v 5]
  let member := truth o (anyT P (pc P "Typing.ctorOk" [sh 2 ms, v 1, labT (v 5),
    childMemberships P (sh 2 ms) (v 5)]) (v 4))
  -- beneath the three quantifiers: the named context v2, the environment v1 and the kernel's
  -- context v0; the clause's context's variables shifted by 3
  let q (i : ℕ) : Term := v (i + 3)
  let ex (i : ℕ) : Term := v (14 + i)
  let cx := c.cx ex (v 2)
  let env := c.env ex (q 3) (v 1)
  let kw := pc P "Reader.resolve" [q 7, q 9, pc P "Reader.expandNums" [q 8,
    c.erasure ex (q 0) (q 1)], scopeOf P (q 8) cx]
  let unindexed (t : Term) : Term :=
    notTest o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [childrenName P, t]])
  imp (Term.eq (Term.snd (v 10)) (pc P "Typing.envMs" [v 5])) <| imp (T.kwsT (v 8)) <|
    imp (S.allL (c.fixedVar (v 8)) (metaAt P (v 0) 1)) <|
    imp (S.allL (c.fixedVar (v 8)) (metaAt P (v 0) 2)) <|
    (c.clauseFlags (v 0)).foldr imp <|
    imp (bodyφ P S T 0 (v 1) (Term.snd (v 2))) <| imp member <|
    (c.extraHyps fun i ↦ v (11 + i)).foldr imp <|
    all (list treeTy) <| all (list treeTy) <| all (list treeTy) <|
    imp (truth o (eqL (labT (q 3)) (labelOf P (q 0)))) <|
    imp (let ct := pc P "Typing.clauseTy" [q 4, q 0, c.fields ex (q 5), q 2, cx]
      Internal.Logic.conj o (isSomeT ct) (Term.eq (get ct) (q 11))) <|
    imp (T.envT (q 10) cx env) <| imp (T.cxT (q 5) cx) <| imp (isSomeT kw) <|
    imp (isSomeT (pc P "Check.typeIn" [q 6, v 0, get kw])) <|
    imp (unindexed (scopeOf P (q 8) (v 2))) <| imp (unindexed (q 9)) <|
    S.conv (Term.lam nat (S.evN (Term.fst (sh 1 (q 10))) (v 0) (sh 1 env) (sh 1 (get kw))))
      (T.relT (q 10) (q 11))

/-- A clause of the chain ({name}`clauseAtφ`): the clause's label's numeral decided present, else
the clause's type refuted, and the scrutinee's label equal to it ({lit}`eqBSound`); the selection of
the constructors of that label of length one, else the type refuted; the selection's first
constructor passing its test ({lit}`ctorUnique`), its label's test decided; the clause
({name}`clause`) at that constructor and the body's typing. -/
def clauseAtWith (c : ChainSpec) (S : Defs) (T : Defs3) : Step :=
  (c.clauseAt, fun ix E ↦ do
    let P := c.prog
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let a : Internal.Thm := ⟨0, clauseAtCtx T ++ c.extra, [], clauseAtφ c P S T⟩
    let nX := c.extra.length
    -- the positions of {name}`clauseAtCtx`'s variables, outside which the further variables are
    let atPos₀ := atPos
    let atPos (k : ℕ) : List Tree → Term := atPos₀ (k + nX)
    let exAt (Γ : List Tree) (i : ℕ) : Term := atPos₀ (nX - i) Γ
    let nF := (c.clauseFlags Term.star).length
    let nE := (c.extraHyps fun _ ↦ Term.star).length
    let oM := nF
    let oX := nF + nE
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    -- positions after the introductions: the common type 0, the relation's context 1, the names 2,
    -- the numeral abbreviations 3, the type abbreviations 4, the globals' types 5, the environment
    -- 6, the constructors 7, the scrutinee 8, the typing 9, the body 10, the metadata 11, the named
    -- context 12, the environment 13 and the kernel's context 14
    let (R, E', specs, t, sr, b, md) := (atPos 1, atPos 6, atPos 7, atPos 8, atPos 9, atPos 10,
      atPos 11)
    let (hMem, hEq, hTy) := (5 + oM, 9 + oX, 10 + oX)
    let unfoldTy : List Internal.NormRule := [.delta (P.idx "Typing.clauseTy")]
    -- the last hypothesis, an equation of trees of distinct labels, refuted by its image by the
    -- truth of the label
    let ctorClash : Deducer := fun Γ Φ ψ ↦
      K.image (Φ.length - 1) (fun u ↦ K.truthB (call D.lab [] [u])) (K.trueOf (dFalse L dHyp))
        Γ Φ ψ
    -- the type's presence and value, split after the hypotheses
    let (hTyS, hTyE) := (17 + oX, 18 + oX)
    let tyFalse (msg : String) : Deducer := linkK K s!"clauseAt: {msg}" fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ hTyS ++ unfoldTy) .full) hTyS (fun Γ Φ ψ ↦
        (dFalse L dHyp Γ Φ ψ).orElse fun _ ↦ ctorClash Γ Φ ψ) Γ Φ ψ
    let j (Γ : List Tree) : Term := pc P "Typing.numTx" [pc P "Typing/Txs.atOr"
      [pc P "Typing.tx0" [], pc P "Typing.elemsTx" [md Γ], leafT bnilT]]
    let getJ (Γ : List Tree) : Term := pc P "Prelude.get" [j Γ]
    let lb (u : Term) : Term := call D.lab [] [u]
    let s (Γ : List Tree) : Term :=
      pc P "Prelude.at" [filterL (labT (t Γ)) (specs Γ), leafT bnilT]
    -- the clause at the constructor s, its type's equation and its test given
    let atClause (iOk iS : ℕ) : Deducer :=
      K.cutThm c.clause (fun Γ ↦ [md Γ, b Γ, Term.snd (sr Γ), t Γ, s Γ, E' Γ, atPos 5 Γ,
          atPos 4 Γ, atPos 3 Γ, atPos 2 Γ, R Γ] ++ c.clauseArgs (exAt Γ)) <|
        K.impE (linkK K "clauseAt: the markers" fun Γ Φ ψ ↦
          (dHyp Γ Φ ψ).orElse fun _ ↦ K.byNorm Γ Φ ψ) <|
        K.impE (linkK K "clauseAt: the keywords" (K.byHyp 1)) <|
        K.impE (linkK K "clauseAt: the variables" (K.byHyp 2)) <|
        K.impE (linkK K "clauseAt: the remaining variables" (K.byHyp 3)) <|
        (List.range nF).foldr
          (fun i k ↦ K.impE (linkK K "clauseAt: the flags" (K.byHyp (4 + i))) k) <|
        K.impE (linkK K "clauseAt: the body" (K.byHyp (4 + oM))) <|
        c.preHyps.foldr
          (fun i k ↦ K.impE (linkK K "clauseAt: further hypothesis" (K.byHyp (6 + oM + i))) k) <|
        K.allEΓ (atPos 12) <| K.allEΓ (atPos 13) <| K.allEΓ (atPos 14) <|
        (c.clauseAlls fun _ ↦ Term.star).zipIdx.foldr (fun (_, i) k ↦ K.allEΓ (fun Γ ↦
          (c.clauseAlls (exAt Γ)).getD i Term.star) k) <|
        K.impE (linkK K "clauseAt: the type" fun Γ Φ ψ ↦
          (K.solve 3 Γ Φ ψ).orElse fun _ ↦ K.byHyp iS Γ Φ ψ) <|
        K.impE (linkK K "clauseAt: the constructor's test" (K.byHyp iOk)) <|
        c.midHyps.foldr
          (fun i k ↦ K.impE (linkK K "clauseAt: further hypothesis" (K.byHyp (6 + oM + i))) k) <|
        K.impE (linkK K "clauseAt: the environment" (K.byHyp (11 + oX))) <|
        K.impE (linkK K "clauseAt: the context" (K.byHyp (12 + oX))) <|
        K.impE (linkK K "clauseAt: the resolution" (K.byHyp (13 + oX))) <|
        K.impE (linkK K "clauseAt: the kernel's typing" (K.byHyp (14 + oX))) <|
        K.impE (linkK K "clauseAt: the scope" (K.byHyp (15 + oX))) <|
        K.impE (linkK K "clauseAt: the names" (K.byHyp (16 + oX))) <|
        linkK K "clauseAt: the conclusion" byLast
    -- the selection's first constructor passes its test, whose label's test holds: the fields'
    -- test, the second conjunct, by normalization
    let unique (iS : ℕ) : Deducer :=
      K.cutThm "ctorUnique" (fun Γ ↦ [specs Γ]) <|
        K.allEΓ (fun Γ ↦ pc P "Typing.envMs" [E' Γ]) <| K.allEΓ (fun Γ ↦ labT (t Γ)) <|
        K.allEΓ (fun Γ ↦ childMemberships P (pc P "Typing.envMs" [E' Γ]) (t Γ)) <|
        K.impE (linkK K "clauseAt: the membership" (K.byHyp hMem)) <|
        K.impE (linkK K "clauseAt: the selection's length" (K.solve 3)) fun Γ Φ ψ ↦
          let iC := Φ.length - 1
          let unfoldOk : List Internal.NormRule := [.delta (P.idx "Typing.ctorOk")]
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ iC ++ unfoldOk) .full) iC (fun Γ Φ ψ ↦
            -- the test unfolded, of index iU: its label's test decided, false refuting it, true
            -- leaving its fields' conjunct
            let iU := Φ.length - 1
            decideIn K (fun Γ ↦ eqL (child0 (s Γ)) (labT (t Γ)))
              (linkK K "clauseAt: the label's test" (K.hypFalse iU))
              (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ iU) .full) iU
                (fun Γ Φ ψ ↦ atClause (Φ.length - 1) iS Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let intros (k : Deducer) : Deducer :=
      (List.range (6 + oX)).foldr (fun _ k ↦ dImpI L k) <|
        (List.range 3).foldr (fun _ k ↦ dAllI L k) <|
        (List.range 8).foldr (fun _ k ↦ dImpI L k) k
    let some d := intros (dConjE L hTy <| decideIn K (fun Γ ↦ pc P "Prelude.isSome" [j Γ])
        (tyFalse "no numeral") <|
      -- the scrutinee's label the numeral's
      K.cutThm "eqBSound" (fun Γ ↦ [lb (getJ Γ)]) <| K.allEΓ (fun Γ ↦ lb (t Γ)) <|
        K.impE (linkK K "clauseAt: the labels' test" (K.byHyp hEq)) <| normLastK K <|
      decideIn K (fun Γ ↦ eqL (pc P "Prelude.length" [filterL (getJ Γ) (specs Γ)])
          (leafT (numeral 1))) (tyFalse "not one constructor") <|
      -- the type's presence and value unfolded, the value's equation a rule
      fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ hTyS ++ unfoldTy) .full) hTyS
        (fun Γ Φ ψ ↦
          let iS := Φ.length - 1
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ hTyE ++ unfoldTy) .full) hTyE (unique iS) Γ Φ ψ)
        Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace s!"{c.clauseAt}: not proved" fun _ ↦ none
    pure (a, d))

/-- The erasure's step at a list node, the head of the spine of the erasure's normal form there. -/
def eraseStepIdx (K : Kit) : Option ℕ := do
  let (z, _) ← evalRw K.G K.E (K.rules []) .full [list treeTy] []
    (pc K.P "Datatype.eraseExpr" [pc K.P "Typing.tList" [v 0]])
  RoseTree.para (fun l (cs : List (Term × Option ℕ)) ↦ match l, cs with
    | .app, [(_, h), _] => h
    | .defn k _, _ => some k
    | _, _ => none) z

/-- The erasure's forced map over a list node's children, as its step writes the node it rebuilds:
in the normal form of the erasure at the node of the list {lit}`xs`, a variable, its step
unfolded, the first application of a right fold over a map over a map over the list, beneath
binders where the list is the variable of index j, its free variables lowered by the binders'
number. -/
def forcedMapOf (K : Kit) (Γ : List Tree) (xs : Term) : Option Term := do
  let k ← eraseStepIdx K
  let (z, _) ← evalRw K.G K.E (K.rules [] ++ [.delta k]) .full Γ []
    (pc K.P "Datatype.eraseExpr" [pc K.P "Typing.tList" [xs]])
  RoseTree.para (fun l (cs : List (Term × Option Term)) ↦
    match cs.findSome? (·.2) with
    | some r => some r
    | none =>
      let u : Term := RoseTree.node l (cs.map Prod.fst)
      match u.label, u.children with
      | .app, [f, _] => match f.label, f.children with
        | .listRec, [_, _, m1] => match m1.label, m1.children with
          | .listRec, [_, _, m2] => match m2.label, m2.children with
            | .listRec, [_, _, x] => match x.label, xs.label with
              | .var j, .var k => some (Term.subst u fun i ↦ v (i - (j - k)))
              | _, _ => none
            | _, _ => none
          | _, _ => none
        | _, _ => none
      | _, _ => none) z

/-- Admitted as a binder by the typing, as a predicate of a tree, at the typing environment
{lit}`E` outside its binder. -/
def binderOk (P : Prog) (E : Term) : Term :=
  Term.lam treeTy (truth P.o (pc P "Typing.binderName" [sh 1 E, v 0]))

/-- The erasure's forced map over a list of trees each admitted as a binder
({name}`forcedMapOf`) is the list: by induction; at a construction, the head an atom, its tree's
node of the atoms' label, which the erasure keeps. In the context of the list and the typing
environment. -/
def eraseAtomsMap (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("eraseAtomsMap", fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let o := P.o
    let Γ := [list treeTy, T.envTy]
    let some fm := forcedMapOf K Γ (v 0) | dbgTrace "eraseAtomsMap: no map" fun _ ↦ none
    let step ← eraseStepIdx K
    let φ := Internal.Logic.imp o (S.allL (binderOk P (v 1)) (v 0)) (Term.eq fm (v 0))
    let byS : Deducer := fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ [.delta step]) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let d₀ ← dImpI L (linkK K "eraseAtomsMap: empty" byS) [T.envTy] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the environment, the head, the rest; hypotheses: the induction hypothesis, the
    -- admissions; the head's node, its label decided an atom's, else its admission false
    let cons : Deducer := dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let adm := Φ₁.length - 1
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₁ adm) .full) adm (K.conjE fun Γ Φ ψ ↦
        let (hd, rest) := (Φ.length - 2, Φ.length - 1)
        -- the induction hypothesis at the rest's admissions, an equation, then the head's node
        dImpE L 0 (K.byHyp rest) (normLastK K fun Γ Φ ψ ↦
          K.treeNode (atPos 1 Γ) (normLastK K fun Γ Φ ψ ↦
            dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
              if bs.map Oitavem.rank == some 1 then
                linkK K "eraseAtomsMap: an atom" byS
              else linkK K s!"eraseAtomsMap: the label {bs.map Oitavem.rank}"
                (K.hypFalse hd))
              3 [] (v 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "eraseAtomsMap: a construction" cons [list treeTy, treeTy, T.envTy]
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The erasure fixes a list of trees each admitted as a binder: its forced map is the list
({name}`eraseAtomsMap`); the list empty, its step's tests fail at once; a construction, its head an
atom, whose name, admitted, is none of the keywords the step rewrites a list headed by
({lit}`Typing.nameOk` rejects them), each test of the head's naming decided, true refuting the
head's admission. In the context of the list and the typing environment. -/
def eraseAtoms (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("eraseAtoms", fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let Γ := [list treeTy, T.envTy]
    let step ← eraseStepIdx K
    let tl := pc P "Typing.tList" [v 0]
    let a : Internal.Thm := ⟨0, Γ, [S.allL (binderOk P (v 1)) (v 0)],
      Term.eq (pc P "Datatype.eraseExpr" [tl]) tl⟩
    let byS : Deducer := fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ [.delta step]) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    -- a test of the head's naming decided, true refuting the head's admission
    let named (kw : String) (adm : ℕ) (hd : List Tree → Term) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Datatype.namedTx" [hd Γ, pc P kw []]) k
        (linkK K s!"eraseAtoms: the head named by {kw}" fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ adm ++
            [.delta (P.idx "Typing.binderName"), .delta (P.idx "Typing.nameOk")]) .full) adm
            (dFalse L dHyp) Γ Φ ψ)
    -- the list split; at a construction, the forced map at the rest the rest
    -- ({name}`eraseAtomsMap`), then the head's node and its naming's tests
    let some d := (fun Γ Φ ψ ↦ K.listCase treeTy (atPos 1 Γ) (linkK K "eraseAtoms: empty" byS)
          (fun Γ Φ ψ ↦
            let (hd, rest) := (atPos (Γ.length - 2), atPos (Γ.length - 1))
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 (K.conjE fun Γ Φ ψ ↦
              let (adm, restAdm) := (Φ.length - 2, Φ.length - 1)
              K.cutThm "eraseAtomsMap" (fun Γ ↦ [rest Γ, atPos 0 Γ]) (K.impE
                (linkK K "eraseAtoms: the rest's admissions" (K.byHyp restAdm)) <|
                normLastK K <|
              K.treeNode (hd Γ) (normLastK K fun Γ Φ ψ ↦
                dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
                  if bs.map Oitavem.rank == some 1 then
                    named "Typing.kwRep" adm hd <| named "Typing.kwDecode" adm hd <|
                    named "Typing.kwDatum" adm hd <| linkK K "eraseAtoms: the list" byS
                  else linkK K s!"eraseAtoms: the label {bs.map Oitavem.rank}"
                    (K.hypFalse adm))
                  3 [] (v 1) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "eraseAtoms: not proved" fun _ ↦ none
    pure (a, d))

/-- The walk of a clause's fields ({name}`walkParts`), present at some field types and named
context, admits each fixed field's variable and the remaining children's as binders: by induction
on the fixed fields' variables, the walk's tests decided, each that leaves it absent refuting its
presence; at none, the remaining variable's binding; at a variable, its admission, then the
induction hypothesis at the walk's rest. In {name}`walkCtx`. -/
def walkBinders (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("walkBinders", fun ix E ↦ do
    let P := { walkProg P with folded := (walkProg P).folded ++ ["Check.typeIn"] }
    let w ← walkParts ⟨P, S, E, ix, []⟩ T
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let o := P.o
    let steps : List Internal.NormRule := ["Typing.bindRest", "Typing.bindVar"].map fun nm ↦
      .delta (P.idx nm)
    let childT ← primT Kernel.Prim.child
    -- under the two quantifiers: the named context v0, the field types v1
    let φ := Internal.Logic.all o (list treeTy) (Term.lam (list treeTy)
      (Internal.Logic.all o (list treeTy) (Term.lam (list treeTy) (Internal.Logic.imp o
        (truth o (pc P "Prelude.isSome" [Term.app (Term.app (sh 2 w.ty) (v 1)) (v 0)]))
        (Internal.Logic.conj o (S.allL (binderOk P (v 7)) (v 2))
          (S.allL (binderOk P (v 7)) (v 5)))))))
    -- the walk's presence, of index 2 after the quantifiers' truths, o after the induction
    -- hypothesis, refuted with the steps unfolded
    let absent (msg : String) (h : ℕ) : Deducer := linkK K s!"walkBinders: {msg}" fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ steps) .full) h (dFalse L dHyp) Γ Φ ψ
    let E' := atPos 5
    let c := atPos 6
    -- a variable's binding at a type: the type's presence, the variable's admission and its not
    -- being the implementation's decided, each false refuting the walk's presence
    let decideBind (h : ℕ) (ty v' : List Tree → Term) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [ty Γ]) (absent "no type" h) <|
      decideIn K (fun Γ ↦ pc P "Typing.binderName" [E' Γ, v' Γ]) (absent "not admitted" h) <|
      decideIn K (fun Γ ↦ pc P "Typing.clauseVar" [E' Γ, v' Γ]) (absent "not a clause's" h) k
    -- no fields: the context outermost first, the relation's context 0 to the body's erasure 9,
    -- the field types 10 and the named context 11; the walk's presence 2
    let splitAt (p : ℕ) (k₀ k₁ : Deducer) : Deducer := fun Γ Φ ψ ↦
      K.listCase treeTy (atPos p Γ) k₀ k₁ Γ Φ ψ
    let nilCase : Deducer := dAllI L <| dAllI L <| dImpI L <|
      splitAt 10
        (decideIn K (fun Γ ↦ apps childT [c Γ, leafT (numeral 2)])
          (splitAt 7 (linkK K "walkBinders: no rest" (K.solve 3))
            (absent "a remaining variable without its field" 2))
          (splitAt 7 (absent "no remaining variable" 2) (fun Γ Φ ψ ↦
            let (pr, pm) := (Γ.length - 2, Γ.length - 1)
            splitAt pm
              (decideBind 2 (fun Γ ↦ pc P "Typing.fieldTy" [E' Γ,
                  apps childT [c Γ, leafT (numeral 3)]]) (atPos pr)
                (linkK K "walkBinders: the remaining variable" (K.solve 3)))
              (absent "two remaining variables" 2) Γ Φ ψ)))
        (absent "a field type without a variable" 2)
    let r₀ := linkK K "walkBinders: no fields" nilCase (walkCtx T).tail []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a fixed field: the relation's context 0 to the body's erasure 9, the variable 10, the rest
    -- 11, the field types 12 and the named context 13; the walk's presence 3
    let consCase : Deducer := dAllI L <| dAllI L <| dImpI L fun Γ Φ ψ ↦
      K.listCase treeTy (atPos 12 Γ) (absent "a variable without a field type" 3)
        (fun Γ Φ ψ ↦
        let (pf, pr) := (Γ.length - 2, Γ.length - 1)
        let (ft, rest) := (atPos pf, atPos pr)
        decideBind 3 (fun Γ ↦ pc P "Typing.fieldTy" [E' Γ, ft Γ]) (atPos 10) (fun Γ Φ ψ ↦
          -- the walk's rest, read off its presence with the steps unfolded: the named context
          -- after the rest of the field types; the induction hypothesis there
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
            | none => dbgTrace "walkBinders: no context" fun _ ↦ none
            | some cx' =>
              dAllE L K.G K.E 0 restT (K.allEΓ (fun _ ↦ cx') <|
                K.impE (linkK K "walkBinders: the rest present" fun Γ Φ ψ ↦
                  dRwHyp (evalRw K.G K.E (K.rulesEx Φ 3 ++ steps) .full) 3
                    (dRwBy (evalRw K.G K.E (K.rules Φ ++ steps) .full) dHyp) Γ Φ ψ) <|
                K.conjE <| linkK K "walkBinders: the variables" fun Γ Φ ψ ↦
                  -- the head's admission decided, the rest's and the remaining children's the
                  -- induction hypothesis's
                  let (iVs, iRvs) := (Φ.length - 2, Φ.length - 1)
                  K.norm (dConjI L (dConjI L (K.solve 3) (K.byHyp iVs)) (K.byHyp iRvs)) Γ Φ ψ)
                Γ Φ ψ) Γ Φ ψ)
        Γ Φ ψ
    let r₁ := linkK K "walkBinders: a field" consCase
      (list treeTy :: treeTy :: (walkCtx T).tail) [Internal.weakenElem φ]
      (Internal.listConsAt 1 treeTy φ)
    let some d₀ := r₀ | dbgTrace "walkBinders: the base not proved" fun _ ↦ none
    let some d₁ := r₁ | dbgTrace "walkBinders: the construction not proved" fun _ ↦ none
    pure (⟨0, walkCtx T, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The erasure at a list node, its step unfolded once: its right side the step's weak head normal
form, normalized with the step kept folded, so that the children's erasures stay single terms. In
the context of the list. Proved by normalizing both sides with the step unfolded. -/
def eraseHead (P : Prog) (S : Defs) : Step :=
  ("eraseHead", fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let step ← eraseStepIdx K
    let Γ := [list treeTy]
    let lhs := pc P "Datatype.eraseExpr" [pc P "Typing.tList" [v 0]]
    let (w, _) ← evalRw K.G K.E (K.rules [] ++ [.delta step]) .head Γ [] lhs
    let (r, _) ← evalRw K.G K.E (K.rules []) .full Γ [] w
    let (l, _) ← evalRw K.G K.E (K.rules []) .full Γ [] lhs
    let a : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let some d := byMode .full K.G K.E 0 (K.rules [] ++ [.delta step]) Γ [] l r
      | dbgTrace "eraseHead: not proved" fun _ ↦ none
    pure (a, d))

/-- The erasure keeps the parts of a clause's metadata the typing and the erasure read: its label's
atom and its variables' lists, where the label's characters are a numeral, the metadata's second
and third elements are lists and their elements are admitted as binders. In the context of the
metadata and the typing environment. Proved by the metadata's node, a list's, else the label
absent; its elements' nodes, the label an atom's, the variables' lists' lists, else a hypothesis
refuted; the step's tests of the label's naming decided, true making its characters a keyword's,
no numeral ({lit}`equalSound`); the variables' lists fixed ({name}`eraseAtoms`). -/
def eraseMetaWith (name listLemma : String) (ok : Prog → Term → Term)
    (extra : Prog → Term → List Term) (prems : ℕ → List ℕ) (P : Prog) (S : Defs) (T : Defs3) :
    Step :=
  (name, fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let o := P.o
    let Γ := [treeTy, T.envTy]
    let er (t : Term) : Term := pc P "Datatype.eraseExpr" [t]
    let isList (t : Term) : Term := truth o (pc P "Datatype.isListTx" [t])
    let nthE (t : Term) (i : ℕ) : Term :=
      pc P "Datatype.nthTx" [pc P "Datatype.elems" [t], leafT (numeral i)]
    let num := truth o (pc P "Prelude.isSome" [pc P "Typing.numTx" [pc P "Typing/Txs.atOr"
      [pc P "Typing.tx0" [], pc P "Typing.elemsTx" [v 0], leafT bnilT]]])
    let goal := Internal.Logic.conj o (Term.eq (labelAtom P (er (v 0))) (labelAtom P (v 0)))
      (Internal.Logic.conj o (Term.eq (metaAt P (er (v 0)) 1) (metaAt P (v 0) 1))
        (Term.eq (metaAt P (er (v 0)) 2) (metaAt P (v 0) 2)))
    let a : Internal.Thm := ⟨0, Γ, [num, isList (nthE (v 0) 1), isList (nthE (v 0) 2),
      S.allL (ok P (v 1)) (metaAt P (v 0) 1), S.allL (ok P (v 1)) (metaAt P (v 0) 2)] ++
        extra P (v 0), goal⟩
    let byS : Deducer := fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let splitAt (p : ℕ) (k₀ k₁ : Deducer) : Deducer := fun Γ Φ ψ ↦
      K.listCase treeTy (atPos p Γ) k₀ k₁ Γ Φ ψ
    -- a tree's node, its label of rank r, else the hypothesis h refuted; k at its children's
    -- position
    let nodeOf (p r h : ℕ) (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
      (linkK K s!"eraseMeta: the node at {p}" <| fun Γ Φ ψ ↦
      K.treeNode (atPos p Γ) (normLastK K fun Γ Φ ψ ↦
        let pc' := Γ.length - 1
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          if bs.map Oitavem.rank == some r then k pc'
          else linkK K s!"eraseMeta: the label {bs.map Oitavem.rank} at {p}" (K.hypFalse h))
          3 [] (v 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    -- the label's naming by a keyword decided; true, the label's name the keyword's, its
    -- characters the keyword's, which are no numeral
    let named (kw : String) (pl : ℕ) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Datatype.namedTx" [atPos pl Γ, pc P kw []]) k
        (linkK K s!"eraseMeta: the label named by {kw}" <|
          K.cutThm "equalSound" (fun Γ ↦ [pc P "Reader.nameOf" [atPos pl Γ]]) <|
          K.allEΓ (fun _ ↦ pc P kw []) <|
          K.impE (linkK K s!"eraseMeta: {kw} equal" (K.solve 3)) fun Γ Φ ψ ↦
          K.image (Φ.length - 1) (fun t ↦ call D.children [] [t])
            -- the label's numeral, the reading of the keyword's characters, unfolded
            (linkK K s!"eraseMeta: {kw} characters" fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ [.delta (P.idx "Reader.numeral")])
                .full) 0 (dFalse L dHyp) Γ Φ ψ) Γ Φ ψ)
    -- a variables' list fixed, the list at position pv, its admissions the hypothesis h
    let fixedList (pv h : ℕ) (k : Deducer) : Deducer :=
      applyThm K listLemma (fun Γ ↦ [atPos pv Γ, atPos 0 Γ])
        ((prems h).map fun i ↦ linkK K s!"eraseMeta: the admissions {i}" (K.byHyp i)) <|
        normLastK K k
    -- the conjunctions split, each equation with the erasure's step unfolded
    let byT : Deducer := fun Γ Φ ψ ↦ (byS Γ Φ ψ).orElse fun _ ↦
      match Internal.eqParts ψ with
      | some (l, r) =>
        let nf (u : Term) := (evalRw K.G K.E (K.rules Φ) .full Γ Φ u).map
          Prod.fst
        let d := (nf l).bind fun x ↦ (nf r).bind fun y ↦ firstDiff x y
        dbgTrace s!"{name}: {d.map fun (x, y) ↦ s!"{showT x}\n vs {showT y}"}" fun _ ↦ none
      | none => none
    let conjS : ℕ → Deducer := fun n ↦ n.rec (fun _ _ _ ↦ none) fun _ rec Γ Φ ψ ↦
      match defnParts ψ with
      | some (i, _, _) => if i = P.o + 1 then dConjI L rec rec Γ Φ ψ else byT Γ Φ ψ
      | none => byT Γ Φ ψ
    -- the erasure's step at the metadata's node unfolded once ({name}`eraseHead`), at its
    -- elements as the splits leave them, then the parts
    let final (pk : ℕ) : Deducer := linkK K "eraseMeta: the parts" fun Γ Φ ψ ↦
      let kids := ((evalRw K.G K.E (K.rules Φ) .full Γ Φ (atPos pk Γ)).map Prod.fst).getD
        Term.star
      (K.cutThm "eraseHead" (fun _ ↦ [kids]) <| normLastK K fun Γ Φ ψ ↦
        dRwBy (evalRw K.G K.E (K.rules Φ) .full) (conjS 4) Γ Φ ψ) Γ Φ ψ
    let refute (msg : String) (h : ℕ) : Deducer := linkK K s!"eraseMeta: {msg}" (K.hypFalse h)
    let some d := (nodeOf 1 2 0 fun pk ↦
        splitAt pk (refute "no elements" 0) <| fun Γ Φ ψ ↦
        let (p0, pr1) := (Γ.length - 2, Γ.length - 1)
        (nodeOf p0 1 0 fun pcs ↦
          decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.numeral" [atPos pcs Γ]])
            (refute "no numeral" 0) <|
          named "Typing.kwRep" p0 <| named "Typing.kwDecode" p0 <| named "Typing.kwDatum" p0 <|
          splitAt pr1 (refute "one element" 1) fun Γ Φ ψ ↦
          let pr2 := Γ.length - 1
          (nodeOf (Γ.length - 2) 2 1 fun pvs ↦ fixedList pvs 3 <|
            splitAt pr2 (refute "two elements" 2) fun Γ Φ ψ ↦
            (nodeOf (Γ.length - 2) 2 2 fun prs ↦ fixedList prs 4 (final pk)) Γ Φ ψ) Γ Φ ψ)
          Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The erasure keeps the parts of a case analysis's clause's metadata ({name}`eraseMetaWith`). -/
def eraseMeta (P : Prog) (S : Defs) (T : Defs3) : Step :=
  eraseMetaWith "eraseMeta" "eraseAtoms" binderOk (fun _ _ ↦ []) (fun h ↦ [h]) P S T

/-- The typing's absent type. -/
def nothingT (P : Prog) : Term := pc P "Typing/OTy.nothing" []

/-- The walk of a clause's fields ({name}`walkParts`) with a body's typing absent at every named
context is absent, at all field types and named contexts: by induction on the fixed fields'
variables. At none, the field types empty or not, then the remaining variable's binding: the
constructor's taking the remaining children decided, the remaining variables' list split, the raw
field type's and the variable's admission decided; at a variable, the field types split, the
field's type and the variable's admission decided, the induction hypothesis at the rest. In
{name}`walkCtx`. -/
def caseFieldsNothing (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("caseFieldsNothing", fun ix E ↦ do
    let P := { walkProg P with folded := (walkProg P).folded ++ ["Check.typeIn"] }
    let w ← walkParts ⟨P, S, E, ix, []⟩ T
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let o := P.o
    let steps : List Internal.NormRule := ["Typing.bindRest", "Typing.bindVar"].map fun nm ↦
      .delta (P.idx nm)
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
    -- the type's presence and the variable's admission decided, each false by normalization
    let decideBind (ty v' : List Tree → Term) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [ty Γ]) byU <|
      decideIn K (fun Γ ↦ pc P "Typing.clauseVar" [atPos 5 Γ, v' Γ]) byU k
    -- the empty walk: positions in the context after the quantifiers, outermost first: the
    -- relation's context 0 to the body's erasure 9, then the field types 10 and the named
    -- context 11
    let c := atPos 6
    let E' := atPos 5
    let nilCase : Deducer := dAllI L <| dAllI L fun Γ Φ ψ ↦
      K.listCase treeTy (atPos 10 Γ)
        (fun Γ Φ ψ ↦ decideIn K (fun Γ ↦ apps childT [c Γ, leafT (numeral 2)])
          (K.listCase treeTy (atPos 7 Γ) byU (fun Γ Φ ψ ↦ byU Γ Φ ψ))
          (fun Γ Φ ψ ↦ K.listCase treeTy (atPos 7 Γ) byU (fun Γ Φ ψ ↦
            let (r, more) := (atPos (Γ.length - 2), atPos (Γ.length - 1))
            K.listCase treeTy (more Γ)
              (decideBind (fun Γ ↦ pc P "Typing.fieldTy" [E' Γ,
                  apps childT [c Γ, leafT (numeral 3)]]) r byU)
              byU Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
        byU Γ Φ ψ
    let r₀ := linkK K "caseFieldsNothing: no fields" nilCase (walkCtx T).tail []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a fixed field: the context after the quantifiers, the relation's context 0 to the body's
    -- erasure 9, the variable 10, the rest 11, the field types 12 and the named context 13
    let consCase : Deducer := dAllI L <| dAllI L fun Γ Φ ψ ↦
      K.listCase treeTy (atPos 12 Γ) byU (fun Γ Φ ψ ↦
        let (ft, rest) := (atPos (Γ.length - 2), atPos (Γ.length - 1))
        decideBind (fun Γ ↦ pc P "Typing.fieldTy" [E' Γ, ft Γ]) (atPos 10) (fun Γ Φ ψ ↦
          -- the induction hypothesis at the rest of the field types and the extended context,
          -- read off the goal with the steps unfolded: the argument after the rest's
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
            | none => dbgTrace "caseFieldsNothing: no context" fun _ ↦ none
            | some cx' =>
              -- the instance normalized with the steps unfolded, as the goal is
              dAllE L K.G K.E 0 restT (K.allEΓ (fun _ ↦ cx') <| (fun k Γ Φ ψ ↦
                dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1) ++ steps) .full)
                  (Φ.length - 1) k Γ Φ ψ) <|
                linkK K "caseFieldsNothing: the rest" byU) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let r₁ := linkK K "caseFieldsNothing: a field" consCase
      (list treeTy :: treeTy :: (walkCtx T).tail) [Internal.weakenElem φ]
      (Internal.listConsAt 1 treeTy φ)
    let some d₀ := r₀ | dbgTrace "caseFieldsNothing: the base not proved" fun _ ↦ none
    let some d₁ := r₁ | dbgTrace "caseFieldsNothing: the construction not proved" fun _ ↦ none
    pure (⟨0, walkCtx T, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The context of the chain of a case analysis's clauses: the clauses' metadata v0, the
scrutinee's tree v1, the constructors v2, the typing environment v3, the kernel's globals' types v4,
the type and numeral abbreviations v5 and v6, the definitions' names v7, the relation's context v8
and the clauses' common type v9. -/
def chainCtx (T : Defs3) : List Tree :=
  [list treeTy, treeTy, list treeTy, T.envTy, list treeTy, list treeTy, list treeTy, list treeTy,
    Defs3.ctxTy, treeTy]

/-- The statement of the chain of a case analysis's clauses, at the metadata v0 of
{name}`chainCtx`: for all bodies' erasures and typings, where the relation's markers are the typing
environment's, no numeral abbreviation names a keyword, the clauses' variables' and labels'
characters are fixed by the expansion of the numeral abbreviations, each body is sound at its
typing, the bodies and the typings are equally many, and the scrutinee is of some constructor;
for all named contexts, environments and kernel's contexts beneath the scrutinee's entry, if an
else clause follows the clauses or one of their labels is the scrutinee's, every type is the
common one, the environment extended by the scrutinee's quotation is related to the named
context extended by its entry, whose names are admitted, the chain's erasure resolves in that
context's scope, of a type in the kernel's context, and the primitives the erasure applies are
named neither in the context's scope nor by a definition, the resolution converges to a value
related at the common type. -/
def chainφ (c : ChainSpec) (K : Kit) (S : Defs) (T : Defs3) : Option Term := do
  let P := K.P
  let o := P.o
  let all (A : Tree) (t : Term) : Term := Internal.Logic.all o A (Term.lam A t)
  let imp := Internal.Logic.imp o
  let conj := Internal.Logic.conj o
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let lenT (xs : Term) : Term := pc P "Typing/Txs.length" [xs]
  let lenS (xs : Term) : Term := pc P "Typing/SRs.length" [xs]
  let lenB (xs : Term) : Term := pc P "Datatype/Txs.length" [xs]
  let headSR (xs : Term) : Term := call D.headD [srTy]
    [Term.pair (leafT bnilT) (Term.lam (list treeTy) (leafT bnilT)), xs]
  let tailSR (xs : Term) : Term := call D.tail [srTy] [xs]
  -- beneath the bodies' and typings' quantifiers: the typings v0, the bodies v1, the metadata
  -- v2, the scrutinee v3, the constructors v4, the environment v5 to the relation's context v10
  -- and the common type v11
  let isList (n : ℕ) : Term := truth o (pc P "Datatype.isListTx"
    [pc P "Datatype.nthTx" [pc P "Datatype.elems" [v 0], leafT (numeral n)]])
  let fixedMeta : Term := Term.lam treeTy (conj (S.allL (c.fixedVar (v 9)) (metaAt P (v 0) 1))
    (conj (S.allL (c.fixedVar (v 9)) (metaAt P (v 0) 2))
      ((c.metaExtra (v 0)).foldr conj
        (conj (Term.app (fixedT P (v 9)) (labelAtom P (v 0))) (conj (isList 1) (isList 2))))))
  let link : Term := Term.app (Term.listRec (Term.lam (list srTy) (Internal.Logic.tt o))
    (Term.lam (list srTy) (conj (bodyφ P S T 3 (v 2) (Term.snd (headSR (v 0))))
      (Term.app (v 1) (tailSR (v 0))))) (v 1)) (v 0)
  let ms := pc P "Typing.envMs" [v 5]
  let member := truth o (anyT P (pc P "Typing.ctorOk" [sh 2 ms, v 1, labT (v 5),
    childMemberships P (sh 2 ms) (v 5)]) (v 4))
  let notLt (a b : Term) : Term := notTest o (ltL a b)
  -- beneath the further quantifiers: the kernel's context v0, the environment v1, the named
  -- context v2, and the above shifted by 3
  let Γ5 : List Tree := [list treeTy, list treeTy, list treeTy, list srTy, list treeTy] ++
    chainCtx T
  let ex (i : ℕ) : Term := v (14 + i)
  let tys ← chainTysWith (c.base ex) (c.fields ex (v 8)) K (Γ5 ++ c.extra) (v 7) (v 5) (v 3) (v 2)
  let cx := c.cx ex (v 2)
  let env := c.env ex (v 6) (v 1)
  let cov := truth o (pc P "Prelude.or" [ltL (lenT (v 5)) (lenS (v 3)),
    anyT P (eqL (labT (v 8)) (v 1)) (labelsT P (v 5))])
  let same := S.allL (Term.lam treeTy (conj (isSomeT (v 0)) (Term.eq (get (v 0)) (v 15)))) tys
  -- the erasure's forced map of the metadata, as the erasure of the case analysis reads it
  let fm ← forcedMapOf K (Γ5 ++ c.extra) (v 5)
  let chain := pc P "Datatype.eraseChain" [c.test.sv, fm, v 4, c.bind ex]
  let kw := pc P "Reader.resolve" [v 10, v 12, pc P "Reader.expandNums" [v 11, chain],
    scopeOf P (v 11) cx]
  let unindexed (n t : Term) : Term :=
    notTest o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [n, t]])
  -- the children primitive's name at the scope's tail, the test's at the scope, as the clause
  -- and the test read them, and none at the definitions' names
  let unscoped := [unindexed (childrenName P) (scopeOf P (v 11) (v 2)),
      unindexed (childrenName P) (v 12)] ++
    (testPrims P).flatMap fun n ↦ [unindexed n (scopeOf P (v 11) cx), unindexed n (v 12)]
  let inner : Term := all (list treeTy) <| all (list treeTy) <| all (list treeTy) <|
    imp cov <| imp same <| imp (T.envT (v 13) cx env) <| imp (T.cxT (v 8) cx) <|
    imp (isSomeT kw) <| imp (isSomeT (pc P "Check.typeIn" [v 9, v 0, get kw])) <|
    unscoped.foldr imp <|
    S.conv (Term.lam nat (S.evN (Term.fst (v 14)) (v 0) (sh 1 env) (sh 1 (get kw))))
      (T.relT (v 13) (v 14))
  pure <| all (list treeTy) <| all (list srTy) <|
    imp (Term.eq (Term.snd (v 10)) (pc P "Typing.envMs" [v 5])) <| imp (T.kwsT (v 8)) <|
    imp (S.allL fixedMeta (v 2)) <| imp link <|
    imp (notLt (lenB (v 1)) (lenS (v 0))) <| imp (notLt (lenS (v 0)) (lenB (v 1))) <|
    imp member <| (c.extraHyps fun i ↦ v (11 + i)).foldr imp inner

/-- The chain of a case analysis's clauses ({name}`chainφ`), by induction on the clauses'
metadata. -/
def chainWith (c : ChainSpec) (S : Defs) (T : Defs3) : Step :=
  (c.name, fun ix E ↦ do
    let P := c.prog
    let K : Kit := ⟨P, S, E, ix, walkRules ix E ++
      lenRules.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let L := K.L
    let φ ← chainφ c K S T
    let nX := c.extra.length
    -- the positions of {name}`chainCtx`'s variables, outside which the further variables are
    let atPos₀ := atPos
    let atPos (k : ℕ) : List Tree → Term := atPos₀ (k + nX)
    let exΓ (i : ℕ) (Γ : List Tree) : Term := atPos₀ (nX - i) Γ
    let ctx := chainCtx T ++ c.extra
    let nE := (c.extraHyps fun _ ↦ Term.star).length
    let childT ← primT Kernel.Prim.child
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    -- a negated hypothesis refuted, its antecedent by normalization
    -- a hypothesis refuted with the expansion of the numeral abbreviations and the reader's
    -- resolution unfolded
    let unfoldedFalse (h : ℕ) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ resolveRules P T ix E ++ [.delta (T.argIdx 3)])
        .full) h (dFalse L dHyp) Γ Φ ψ
    let notFalse (msg : String) (h : ℕ) : Deducer := linkK K s!"chain: {msg}" <|
      fun Γ Φ ψ ↦ dImpE L h (K.solve 3) lastFalse Γ Φ ψ
    -- the hypotheses after the introductions, o after the induction hypothesis: the bodies' and
    -- the typings' quantifiers' truths, the markers, the keywords, the characters, the bodies'
    -- soundness, the comparisons of the bodies' and the typings' lengths, the scrutinee's
    -- constructor; the further
    -- quantifiers' truths, the labels' covering, the common type, the environment's relation, the
    -- context's names, the resolution, the kernel's typing and the primitives' names
    let (hKw, hFix, hLink, hBS, hSB, hMem) :=
      ((· + 3), (· + 4), (· + 5), (· + 6), (· + 7), (· + 8))
    let (hCov, hSame, hEnv, hCx, hRes, hKer) :=
      ((· + 12 + nE), (· + 13 + nE), (· + 14 + nE), (· + 15 + nE), (· + 16 + nE), (· + 17 + nE))
    let hUn (o i : ℕ) : ℕ := o + 18 + nE + i
    let hXt (o i : ℕ) : ℕ := o + 9 + i
    let intros (k : Deducer) : Deducer :=
      dAllI L <| dAllI L <| (List.range (7 + nE)).foldr (fun _ k ↦ dImpI L k) <|
        (List.range 3).foldr (fun _ k ↦ dAllI L k) <| (List.range 12).foldr (fun _ k ↦ dImpI L k) k
    -- the base: positions in the context after the introductions, the common type 0, the
    -- relation's context 1, the names 2, the numeral abbreviations 3, the type abbreviations 4,
    -- the globals' types 5, the environment 6, the constructors 7, the scrutinee 8, the bodies 9,
    -- the typings 10, the named context 11, the environment 12 and the kernel's context 13
    let exAt (Γ : List Tree) (i : ℕ) : Term := exΓ i Γ
    let cxS (Γ : List Tree) : Term := c.cx (exAt Γ) (atPos 11 Γ)
    let envS (Γ : List Tree) : Term := c.env (exAt Γ) (atPos 8 Γ) (atPos 12 Γ)
    -- the else clause's body, of position pB, sound at its typing: the bodies' soundness at the
    -- named context, the environment and the kernel's context extended by the scrutinee
    let elseBody : Deducer := linkK K "chain: the else clause" <|
      fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ (hLink 0)) .full) (hLink 0) (K.conjE fun Γ Φ ψ ↦
        let body := Φ.length - 2
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ (hSame 0)) .full) (hSame 0) (K.conjE fun Γ Φ ψ ↦
          -- the else clause's type present, its value the common type's
          dConjE L (Φ.length - 2) (fun Γ Φ ψ ↦
          let sameHd := Φ.length - 2
          dAllE L K.G K.E body (cxS Γ) (K.allEΓ envS <| K.allEΓ (atPos 13) <|
            K.impE (linkK K "chain: the else body's environment" (K.byHyp (hEnv 0))) <|
            K.impE (linkK K "chain: the else body's typing" (K.byHyp sameHd)) <|
            K.impE (linkK K "chain: the else body's resolution" (K.byHyp (hRes 0))) <|
            K.impE (linkK K "chain: the else body's kernel typing" (K.byHyp (hKer 0))) <|
            K.impE (linkK K "chain: the else body's context" (K.byHyp (hCx 0))) <|
            linkK K "chain: the else body's conclusion" byLast) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let base : Deducer := intros fun Γ Φ ψ ↦
      K.listCase treeTy (atPos 9 Γ)
        (linkK K "chain: no body" (unfoldedFalse (hRes 0)))
        (fun Γ Φ ψ ↦ K.listCase srTy (atPos 10 Γ) (notFalse "no typing" (hSB 0)) elseBody Γ Φ ψ)
        Γ Φ ψ
    let r₀ := linkK K "chain: no clause" base ctx.tail []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a construction: positions in the context after the introductions, the common type 0 to the
    -- scrutinee 8 as in the base, the head's metadata 9, the rest's 10, the bodies 11, the typings
    -- 12, the named context 13, the environment 14 and the kernel's context 15; after the bodies'
    -- and the typings' case analyses, the body 16, the bodies after it 17, the typing 18 and the
    -- typings after it 19
    let o := 1
    let (m, ms) := (atPos 9, atPos 10)
    let (b, sr) := (atPos 16, atPos 18)
    let envC (Γ : List Tree) : Term := c.env (exAt Γ) (atPos 8 Γ) (atPos 14 Γ)
    -- the conjunction of index h normalized and split, its parts given to k by their indices
    let split (h : ℕ) (k : ℕ → ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h (K.conjE fun Γ Φ ψ ↦
        k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    -- the clause at the head, its body and typing, the parts of the characters' hypotheses, the
    -- body's soundness and the type's equation given
    let atHead (iVars iRest iBody iTy : ℕ) (iExtras : List ℕ) (iEq : Deducer)
        (res : Deducer := K.byHyp (hRes o)) (ker : Deducer := K.byHyp (hKer o)) : Deducer :=
      K.cutThm c.clauseAt (fun Γ ↦ [m Γ, b Γ, sr Γ, atPos 8 Γ, atPos 7 Γ, atPos 6 Γ, atPos 5 Γ,
          atPos 4 Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ] ++
          (List.range nX).map fun i ↦ exΓ (i + 1) Γ) <|
        K.impE (linkK K "chain: the markers" fun Γ Φ ψ ↦
          (dHyp Γ Φ ψ).orElse fun _ ↦ K.byNorm Γ Φ ψ) <|
        K.impE (linkK K "chain: the keywords" (K.byHyp (hKw o))) <|
        K.impE (linkK K "chain: the variables" (K.byHyp iVars)) <|
        K.impE (linkK K "chain: the remaining variables" (K.byHyp iRest)) <|
        (iExtras.take (c.clauseFlags Term.star).length).foldr
          (fun i k ↦ K.impE (linkK K "chain: the entries' flags" (K.byHyp i)) k) <|
        K.impE (linkK K "chain: the body" (K.byHyp iBody)) <|
        K.impE (linkK K "chain: the membership" (K.byHyp (hMem o))) <|
        (List.range nE).foldr
          (fun i k ↦ K.impE (linkK K s!"chain: further hypothesis {i}" (K.byHyp (hXt o i))) k) <|
        K.allEΓ (atPos 13) <| K.allEΓ (atPos 14) <| K.allEΓ (atPos 15) <|
        K.impE (linkK K "chain: the labels" iEq) <|
        -- the type's equation, a rule of the normalization, as written or reflexive
        K.impE (linkK K "chain: the type" fun Γ Φ ψ ↦
          ((dHyp Γ Φ ψ).orElse fun _ ↦ K.byNorm Γ Φ ψ).orElse fun _ ↦ K.byHyp iTy Γ Φ ψ) <|
        K.impE (linkK K "chain: the environment" (K.byHyp (hEnv o))) <|
        K.impE (linkK K "chain: the context" (K.byHyp (hCx o))) <|
        K.impE (linkK K "chain: the resolution" res) <|
        K.impE (linkK K "chain: the kernel's typing" ker) <|
        K.impE (linkK K "chain: the scope" (K.byHyp (hUn o 0))) <|
        K.impE (linkK K "chain: the names" (K.byHyp (hUn o 1))) <|
        linkK K "chain: the clause's conclusion" byLast
    let Kt : Kit := { K with more := K.more.filter (· ≠ "indexOfCons") }
    let unfoldW : List Internal.NormRule := c.walkDefs.map fun nm ↦ .delta (P.idx nm)
    let unfoldTy : List Internal.NormRule :=
      [.delta (P.idx "Typing.clauseTy"), .delta (P.idx "Typing.numTx")]
    -- a clause's type refuted, its label's numeral absent or its constructor not one
    let tyFalse (msg : String) (iTy : ℕ) : Deducer := linkK K s!"chain: {msg}" fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ iTy ++ unfoldTy) .full) iTy (K.conjE fun Γ Φ ψ ↦
        (K.hypFalse (Φ.length - 2) Γ Φ ψ).orElse fun _ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    -- a clause without a typing, of metadata md, its type's equation of index iEq refuted: the
    -- label's numeral and the constructor decided, then the walk at the absent body absent
    -- ({name}`caseFieldsNothing`)
    let nothingTy (msg : String) (iEq : ℕ) (md : List Tree → Term) : Deducer :=
      let j (Γ : List Tree) : Term := pc P "Typing.numTx" [pc P "Typing/Txs.atOr"
        [pc P "Typing.tx0" [], pc P "Typing.elemsTx" [md Γ], leafT bnilT]]
      let ss (Γ : List Tree) : Term := filterL (pc P "Prelude.get" [j Γ]) (atPos 7 Γ)
      let sC (Γ : List Tree) : Term := pc P "Prelude.at" [ss Γ, leafT bnilT]
      let unfoldF : List Internal.NormRule := [.delta (P.idx c.fieldsDef)]
      linkK K s!"chain: {msg}" <|
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [j Γ]) (tyFalse s!"{msg}: no numeral" iEq) <|
      decideIn K (fun Γ ↦ eqL (pc P "Prelude.length" [ss Γ]) (leafT (numeral 1)))
        (tyFalse s!"{msg}: not one constructor" iEq) <| fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ iEq ++ unfoldTy ++ unfoldF) .full) iEq
        (K.conjE fun Γ Φ ψ ↦
          let iS := Φ.length - 2
          let fts (Γ : List Tree) : Term := call D.children [] [apps childT [sC Γ,
            leafT (numeral 1)]]
          let cxW (Γ : List Tree) : Term := c.cxWalk (exAt Γ) (atPos 13 Γ)
          (K.cutThm c.fieldsNothing (fun Γ ↦ [metaAt P (md Γ) 1, leafT bnilT,
              Term.lam (list treeTy) (nothingT P), metaAt P (md Γ) 2, sC Γ, atPos 6 Γ,
              atPos 5 Γ, atPos 4 Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ] ++ c.walkExtra (exAt Γ)) <|
            -- the type's presence normalized by the instance: the type absent
            K.allEΓ fts <| K.allEΓ cxW <| fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1) ++ unfoldW) .full) (Φ.length - 1)
                (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ iS ++ unfoldW) .full) iS
                  (dFalse L dHyp) Γ Φ ψ) Γ Φ ψ)
            Γ Φ ψ)
        Γ Φ ψ
    -- all the parts of the hypotheses at the head and at the rest: the head's variables', its
    -- remaining variables' and its label's characters, the rest's; the body's soundness, the
    -- rest's; the head's type, the rest's
    let nM := (c.metaExtra Term.star).length
    -- the further conjuncts split in turn, their indices given to k
    let extras : ℕ → (List ℕ → Deducer) → Deducer := fun n k ↦
      (n.rec (motive := fun _ ↦ List ℕ → Deducer) (fun acc ↦ k acc.reverse) fun _ rec acc ↦
        fun Γ Φ ψ ↦ dConjE L (Φ.length - 1) (fun Γ Φ ψ ↦
          rec ((Φ.length - 2) :: acc) Γ Φ ψ) Γ Φ ψ) []
    let partsAll (k : List ℕ → Deducer) : Deducer :=
      split (hFix o) fun iM iFixRest ↦ fun Γ Φ ψ ↦ dConjE L iM (fun Γ Φ ψ ↦
        let iVars := Φ.length - 2
        dConjE L (Φ.length - 1) (fun Γ Φ ψ ↦
          let iRest := Φ.length - 2
          extras nM (fun iXs ↦ fun Γ Φ ψ ↦ dConjE L (Φ.length - 1) (fun Γ Φ ψ ↦
            let iLab := Φ.length - 2
            dConjE L (Φ.length - 1) (fun Γ Φ ψ ↦
              let (iS1, iS2) := (Φ.length - 2, Φ.length - 1)
              split (hLink o) (fun iBody iLinkRest ↦ split (hSame o) fun iTy iTysRest ↦
                k ([iVars, iRest, iLab, iBody, iTy, iFixRest, iLinkRest, iTysRest, iS1, iS2] ++
                  iXs))
                Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    -- the head's metadata's parts as the erasure reads them, its own: the head's type's label
    -- and constructor decided, the walk then present, its variables admitted
    -- ({name}`walkBinders`), the erasure's parts the metadata's ({name}`eraseMeta`), each
    -- equation a rule
    let erasedHead (ps : List ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
      let iTy ← ps[4]?
      let iS1 ← ps[8]?
      let iS2 ← ps[9]?
      let j (Γ : List Tree) : Term := pc P "Typing.numTx" [pc P "Typing/Txs.atOr"
        [pc P "Typing.tx0" [], pc P "Typing.elemsTx" [m Γ], leafT bnilT]]
      let ss (Γ : List Tree) : Term := filterL (pc P "Prelude.get" [j Γ]) (atPos 7 Γ)
      let sC (Γ : List Tree) : Term := pc P "Prelude.at" [ss Γ, leafT bnilT]
      let unfoldF : List Internal.NormRule := [.delta (P.idx c.fieldsDef)]
      let fts (Γ : List Tree) : Term := call D.children [] [apps childT [sC Γ,
        leafT (numeral 1)]]
      let cxW (Γ : List Tree) : Term := c.cxWalk (exAt Γ) (atPos 13 Γ)
      (linkK K "chain: the head's erasure" <|
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [j Γ]) (tyFalse "the head: no numeral" iTy) <|
      decideIn K (fun Γ ↦ eqL (pc P "Prelude.length" [ss Γ]) (leafT (numeral 1)))
        (tyFalse "the head: not one constructor" iTy) <| fun Γ Φ ψ ↦
      -- the walk's equation, the type's unfolded
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ iTy ++ unfoldTy ++ unfoldF) .full) iTy
        (K.conjE fun Γ Φ ψ ↦
         let iS := Φ.length - 2
         (K.cutThm c.walkBinders (fun Γ ↦ [metaAt P (m Γ) 1, leafT bnilT, Term.snd (sr Γ),
            metaAt P (m Γ) 2, sC Γ, atPos 6 Γ, atPos 5 Γ, atPos 4 Γ, atPos 3 Γ, atPos 2 Γ,
            atPos 1 Γ] ++ c.walkExtra (exAt Γ)) <|
          K.allEΓ fts <| K.allEΓ cxW <|
          K.impE (linkK K "chain: the head's walk present" fun Γ Φ ψ ↦
            (K.solve 3 Γ Φ ψ).orElse fun _ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ iS ++ unfoldW) .full) iS
                (dRwBy (evalRw K.G K.E (K.rules Φ ++ unfoldW) .full) dHyp) Γ Φ ψ) <|
          K.conjE fun Γ Φ ψ ↦
          let (iBV, iBR) := (Φ.length - 2, Φ.length - 1)
          applyThm K c.eraseMeta (fun Γ ↦ [m Γ, atPos 6 Γ])
            ([linkK K "chain: the head's numeral" (K.solve 3), K.byHyp iS1, K.byHyp iS2,
              K.byHyp iBV, K.byHyp iBR] ++ (ps.drop 10).map K.byHyp)
            (normLastK K <| K.conjE <| K.conjE k) Γ Φ ψ)
          Γ Φ ψ)
        Γ Φ ψ) Γ Φ ψ
    -- the last clause, untested: no clause after it, else too few typings; the labels' equation
    -- by the covering
    let untested : Deducer := linkK K "chain: the last clause" <|
      fun Γ Φ ψ ↦ K.listCase srTy (atPos 19 Γ)
        (fun Γ Φ ψ ↦ K.listCase treeTy (ms Γ)
          (partsAll fun ps ↦ erasedHead ps <|
            atHead (ps.getD 0 0) (ps.getD 1 0) (ps.getD 3 0) (ps.getD 4 0) (ps.drop 10) <|
              decideIn K (fun Γ ↦ eqL (labT (atPos 8 Γ)) (labelOf P (m Γ)))
                (linkK K "chain: the last label" (K.hypFalse (hCov o))) (K.solve 3))
          -- a clause after the last body, untyped
          (fun Γ Φ ψ ↦
            let m2 := atPos₀ (Γ.length - 2)
            partsAll (fun ps ↦ split (ps.getD 7 0) fun iTy2 _ ↦
              nothingTy "a clause after the last body" iTy2 m2) Γ Φ ψ) Γ Φ ψ)
        (notFalse "a typing after the last body" (hBS o)) Γ Φ ψ
    -- a tested clause, the bodies after it b2 at 20 and bs' at 21
    let (b2, bs') := (atPos 20, atPos 21)
    let rest (Γ : List Tree) : Term :=
      pc P "Datatype.eraseChain" [c.test.sv,
        (forcedMapOf K Γ (ms Γ)).getD Term.star, consT treeTy (b2 Γ) (bs' Γ), c.bind (exAt Γ)]
    let en (Γ : List Tree) (t : Term) : Term := pc P "Reader.expandNums" [atPos 3 Γ, t]
    let scS (Γ : List Tree) : Term := c.test.scope (scopeOf P (atPos 3 Γ) (atPos 13 Γ))
    let rv (Γ : List Tree) (t : Term) : Term :=
      pc P "Reader.resolve" [atPos 4 Γ, atPos 2 Γ, t, scS Γ]
    let clauseE (Γ : List Tree) : Term := en Γ (c.erasure (exAt Γ) (m Γ) (b Γ))
    let restE (Γ : List Tree) : Term := en Γ (rest Γ)
    -- the label's name, a numeral, not abbreviated: the keywords' coherence refuted by the
    -- disjunction's last part, the characters' numeral, the index kept folded
    let labelPlain (n : List Tree → Term) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [n Γ, atPos 3 Γ]]) k
        (linkK K "chain: the label abbreviated" <|
          dRwHyp (evalRw K.G K.E [.delta (T.q + 5 + 2 * nFolds)] .head) (hKw o) <|
          Kt.allEΓ n <| Kt.impE (Kt.solve 3) <| Kt.impE (fun Γ Φ ψ ↦
            let impl := pc P "implName" [n Γ]
            let num := pc P "Prelude.isSome" [pc P "Reader.numeral" [call D.children [] [n Γ]]]
            let reserved := pc P "Prelude.isSome" [pc P "Reader.indexOf"
              [n Γ, pc P "Reader.reservedNames" []]]
            applyThm Kt "orRightT" (fun _ ↦ [pc P "Prelude.or" [impl, num], reserved])
              [applyThm Kt "orRightT" (fun _ ↦ [num, impl]) [Kt.solve 3] dHyp] dHyp Γ Φ ψ)
            lastFalse)
    -- a hypothesis as written, else normalized
    let hypOr (msg : String) (i : ℕ) : Deducer := linkK K s!"chain: the rest's {msg}" fun Γ Φ ψ ↦
      (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp i Γ Φ ψ
    let testedBody (ps : List ℕ) (pC : ℕ) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦ do
      let [iVars, iRest, iLab, iBody, iTy, iFixRest, iLinkRest, iTysRest, _, _] := ps.take 10
        | none
      let cs := atPos₀ pC
      let nodeN (Γ : List Tree) : Term := nodeT (Term.pair (numeral 0) (cs Γ))
      let negated : Deducer := dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
      -- the builders' equations cut in, each normalized a rule under those before it: the
      -- test's expansion first, which the conditional's then contains as the test itself
      let eqs (k : Deducer) : Deducer :=
        applyThm K c.test.nums (fun Γ ↦ [cs Γ, atPos 3 Γ])
          [negated, negated, negated, negated,
            linkK K "chain: the label's characters"
              (dImpE L iLab (linkK K "chain: the label an atom" (K.solve 3))
                fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)] <| normLastK K <|
        applyThm K "ifNums" (fun Γ ↦ [rest Γ, c.erasure (exAt Γ) (m Γ) (b Γ),
            testAt P c.test.sv (cs Γ), atPos 3 Γ]) [negated] <| normLastK K <|
        applyThm K "ifRes" (fun Γ ↦ [restE Γ, clauseE Γ, testAt P c.test.sv (cs Γ), scS Γ,
            atPos 4 Γ, atPos 2 Γ]) [] <| normLastK K <|
        applyThm K c.test.res (fun Γ ↦ [cs Γ, scopeOf P (atPos 3 Γ) (atPos 13 Γ), atPos 4 Γ,
            atPos 2 Γ])
          [K.solve 3, K.byHyp (hUn o 2), K.byHyp (hUn o 3), K.byHyp (hUn o 4),
            K.byHyp (hUn o 5)] <| normLastK K k
      -- the clause's and the rest's resolutions present, else the chain's refuted
      let present (k : Deducer) : Deducer :=
        decideOpt K (fun Γ ↦ rv Γ (clauseE Γ))
          (linkK K "chain: the clause unresolved" (K.hypFalse (hRes o))) <|
        decideOpt K (fun Γ ↦ rv Γ (restE Γ))
          (linkK K "chain: the rest unresolved" (K.hypFalse (hRes o))) k
      -- the kernel's terms of the test, the clause and the rest
      let testK (Γ : List Tree) : Term :=
        let r := ((K.E[K.ix c.test.res]?).bind fun e ↦ match e with
          | Internal.Entry.language b => (Internal.eqParts b.concl).map Prod.snd
          | _ => none).getD Term.star
        pc P "Prelude.get" [Term.subst r fun i ↦ if i = 0 then cs Γ else Term.star]
      let aK (Γ : List Tree) : Term := pc P "Prelude.get" [rv Γ (clauseE Γ)]
      let bK (Γ : List Tree) : Term := pc P "Prelude.get" [rv Γ (restE Γ)]
      let xT (Γ : List Tree) : Term :=
        eqL (labT (atPos 8 Γ)) (pc P "Prelude.get" [pc P "Reader.numeral" [cs Γ]])
      let ih (iTb : ℕ) : Deducer := linkK K "chain: the rest" <| fun Γ Φ ψ ↦
        (dAllE L K.G K.E 0 (consT treeTy (b2 Γ) (bs' Γ)) <| K.allEΓ (atPos 19) <|
        K.impE (linkK K "chain: the rest's markers" fun Γ Φ ψ ↦
          (dHyp Γ Φ ψ).orElse fun _ ↦ K.byNorm Γ Φ ψ) <|
        K.impE (hypOr "the keywords" (hKw o)) <| K.impE (hypOr "the characters" iFixRest) <|
        K.impE (linkK K "chain: the rest's bodies" fun Γ Φ ψ ↦
          -- the typings' tail, by the prelude's rebuilding fold, the typings after the head
          let reb : List Internal.NormRule := [.thm (ix "rebT") [srTy]]
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ iLinkRest ++ reb) .full) iLinkRest
            (dRwBy (evalRw K.G K.E (K.rules Φ ++ reb) .full) dHyp) Γ Φ ψ) <|
        K.impE (hypOr "the lengths 1" (hBS o)) <|
        K.impE (hypOr "the lengths 2" (hSB o)) <|
        K.impE (hypOr "the membership" (hMem o)) <|
        (List.range nE).foldr (fun i k ↦ K.impE (hypOr s!"further hypothesis {i}" (hXt o i)) k) <|
        K.allEΓ (atPos 13) <| K.allEΓ (atPos 14) <| K.allEΓ (atPos 15) <|
        K.impE (hypOr "the covering" (hCov o)) <|
        K.impE (linkK K "chain: the rest's types" fun Γ Φ ψ ↦
          -- the typings' tail, by the case analysis's rebuilding, the typings after the head
          let reb : List Internal.NormRule :=
            [.thm (ix "rebT") [srTy], .thm (ix "rebL") [srTy, list srTy]]
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ iTysRest ++ reb) .full) iTysRest
            (dRwBy (evalRw K.G K.E (K.rules Φ ++ reb) .full) dHyp) Γ Φ ψ) <|
        K.impE (hypOr "the environment" (hEnv o)) <| K.impE (hypOr "the context" (hCx o)) <|
        K.impE (linkK K "chain: the rest's resolution" (K.solve 3)) <|
        K.impE (hypOr "the kernel typing" iTb) <|
        (List.range 6).foldr (fun i k ↦ K.impE (hypOr s!"the names {i}" (hUn o i)) k)
          (linkK K "chain: the rest's conclusion" byLast)) Γ Φ ψ
      let branches (iTa iTb : ℕ) : Deducer :=
        decideIn K (fun Γ ↦ xT Γ) (ih iTb)
          (atHead iVars iRest iBody iTy (ps.drop 10) (K.solve 3) (K.solve 3) (K.byHyp iTa))
      let evalCond : Deducer := fun Γ Φ ψ ↦
        applyThm K "condTyped" (fun Γ ↦ [testK Γ, aK Γ, bK Γ, atPos 15 Γ, atPos 5 Γ])
          [linkK K "chain: the conditional's typing" (K.byHyp (hKer o))] (K.conjE fun Γ Φ ψ ↦
          let (iTa, iTb) := (Φ.length - 2, Φ.length - 1)
          applyThm K "condConv" (fun Γ ↦ [envC Γ, testK Γ, aK Γ, bK Γ,
              T.relT (atPos 1 Γ) (atPos 0 Γ), atPos 1 Γ, xT Γ])
            [linkK K "chain: the test's value" <|
              K.cutThm c.test.conv (fun Γ ↦ [atPos 14 Γ, atPos 8 Γ, atPos 1 Γ, cs Γ] ++
                c.testExtra (exAt Γ)) byLast,
              linkK K "chain: the branch" (branches iTa iTb)]
            (linkK K "chain: the conditional's conclusion" byLast) Γ Φ ψ) Γ Φ ψ
      (plainAtoms K T ([pc P "Reader.kwIf" [], atomNameT (pc P "Datatype.aEq" []),
          atomNameT (pc P "Datatype.aLabel" []), c.test.svName] ++ c.scopeNames.map Prod.fst)
          (atPos 3) (hKw o)
          (labelPlain nodeN (eqs (present evalCond)))
          (lemmas := [(pc P "Reader.kwIf" [], "ifExcluded"),
            (atomNameT (pc P "Datatype.aEq" []), "eqExcluded"),
            (atomNameT (pc P "Datatype.aLabel" []), "labelExcluded"),
            (c.test.svName, c.svExcluded)] ++ c.scopeNames)) Γ₀ Φ₀ ψ₀
    let tested : Deducer := linkK K "chain: a tested clause" <| partsAll fun ps ↦
      let iTy := ps.getD 4 0
      -- the label's atom a node: of the atoms' label, its characters a numeral, else the head's
      -- type refuted
      erasedHead ps fun Γ Φ ψ ↦ K.treeNode (labelAtom P (m Γ))
        (normLastK K fun Γ Φ ψ ↦
          let pC := Γ.length - 1
          dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
            if bs.map Oitavem.rank == some 1 then
              decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.numeral" [atPos₀ pC Γ]])
                (tyFalse "the label no numeral" iTy) (testedBody ps pC)
            else tyFalse s!"the label's node of label {bs.map Oitavem.rank}" iTy)
            3 [] (v 1) Γ Φ ψ) Γ Φ ψ
    let consCase : Deducer := intros fun Γ Φ ψ ↦
      K.listCase treeTy (atPos 11 Γ)
        (fun Γ Φ ψ ↦ K.listCase srTy (atPos 12 Γ)
          (split (hSame o) fun iTy _ ↦ nothingTy "no body, no typing" iTy m)
          (notFalse "no body" (hBS o)) Γ Φ ψ)
        (fun Γ Φ ψ ↦ K.listCase srTy (atPos 12 Γ) (notFalse "no typing" (hSB o))
          (fun Γ Φ ψ ↦ K.listCase treeTy (atPos 17 Γ) untested tested Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let r₁ := linkK K "chain: a clause" consCase
      (list treeTy :: treeTy :: ctx.tail) [Internal.weakenElem φ]
      (Internal.listConsAt 1 treeTy φ)
    let some d₀ := r₀ | dbgTrace "chain: the base not proved" fun _ ↦ none
    let some d₁ := r₁ | dbgTrace "chain: the construction not proved" fun _ ↦ none
    pure (⟨0, ctx, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The chain of a case analysis's clauses: the scrutinee's entry alone around them. -/
def caseChain (P : Prog) : ChainSpec where
  name := "chain"
  prog := chainProg P
  test := caseTest (chainProg P)
  extra := []
  cx := fun _ inner ↦ consT treeTy (scrutineeEntry (chainProg P)) inner
  env := fun _ t e ↦ consT treeTy (pc (chainProg P) "Eval.valQuote" [t]) e
  base := fun _ ↦ scrutineeBase (chainProg P)
  fields := fun _ E ↦ caseFieldsFn (chainProg P) E
  bind := fun _ ↦ bindFn (chainProg P)
  erasure := fun _ md b ↦ clauseErasure (chainProg P) md b
  fixedVar := fixedT (chainProg P)
  metaExtra := fun _ ↦ []
  extraHyps := fun _ ↦ []
  clauseAt := "clauseAt"
  fieldsNothing := "caseFieldsNothing"
  walkBinders := "walkBinders"
  eraseMeta := "eraseMeta"
  fieldsDef := "Typing.caseFields"
  walkDefs := []
  cxWalk := fun _ inner ↦ consT treeTy (fieldsEntry (chainProg P))
    (consT treeTy (scrutineeEntry (chainProg P)) inner)
  walkExtra := fun _ ↦ []
  testExtra := fun _ ↦ []
  clause := "clause"
  clauseArgs := fun _ ↦ []
  clauseFlags := fun _ ↦ []
  preHyps := []
  clauseAlls := fun _ ↦ []
  midHyps := []
  svExcluded := "scrutExcluded"
  scopeNames := []

/-- The chain of a case analysis's clauses ({name}`chainWith`). -/
def chain (P : Prog) (S : Defs) (T : Defs3) : Step := chainWith (caseChain P) S T

/-- A clause of the chain of a case analysis's clauses ({name}`clauseAtWith`). -/
def clauseAt (P : Prog) (S : Defs) (T : Defs3) : Step := clauseAtWith (caseChain P) S T

/-- The index of a key among the markers' names, by the reader's index. -/
def markerIdx (P : Prog) (k xs : Term) : Term :=
  pc P "Reader.indexOf" [k, pc P "Typing.markerNames" [xs]]

/-- At the index of a key among a list of markers' names, where it has one, the list's map by a
function is the function at the marker of that index, as the typing reads it
({lit}`Typing/Txs.atOr`):
by induction on the markers; at a construction, the key the head's name or not. Equal, the index
is the first, the map's head the function at the head; unequal, the index is the rest's
successor, at which both lists' lookups are the rest's, and the induction hypothesis. In the
context of the markers, under the function and the key. -/
def atIndexMap (P : Prog) (S : Defs) : Step :=
  ("atIndexMap", fun ix E ↦ do
    let K : Kit := ⟨caseProg P, S, E, ix, ["indexOfCons", "indexOfNil"].filter
      fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let L := K.L
    let o := P.o
    let F := exp treeTy treeTy
    let succRules : List Internal.NormRule :=
      [.thm (ix "rIterSucc") [list treeTy], .thm (ix "addOne") []]
    -- under the quantifiers: the key v0, the function v1, the markers v2
    let idx := markerIdx P (v 0) (v 2)
    let φ := Internal.Logic.all o F (Term.lam F (Internal.Logic.all o treeTy (Term.lam treeTy
      (Internal.Logic.imp o (truth o (pc P "Prelude.isSome" [idx]))
        (Term.eq (pc P "Prelude.at" [mapFnT (v 1) (v 2), pc P "Prelude.get" [idx]])
          (Term.app (v 1) (pc P "Typing/Txs.atOr" [pc P "Typing.tx0" [], v 2,
            pc P "Prelude.get" [idx]])))))))
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let d₀ ← dAllI L (dAllI L (dImpI L (linkK K "atIndexMap: empty" lastFalse))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the key, the function, the rest, the head; hypotheses: the induction hypothesis,
    -- the index's presence
    let cons : Deducer := dAllI L <| dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let (hd, tl, g, key) := (at_ 0, at_ 1, at_ 2, at_ 3)
      let byNormS : Deducer := fun Γ Φ ψ ↦
        dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ succRules) Γ
          (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
      let restIdx (Γ : List Tree) : Term := pc P "Prelude.isSome" [markerIdx P (key Γ) (tl Γ)]
      let rest : Deducer := linkK K "atIndexMap: the rest" <|
        decideIn K restIdx (linkK K "atIndexMap: no index" (K.hypFalse (Φ₁.length - 1)))
          (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (g Γ) (K.allEΓ key <| K.impE (K.solve 3) <|
            normLastK K <| linkK K "atIndexMap: the rest's equation" byNormS) Γ Φ ψ)
      let equalT := (primT Kernel.Prim.equal).getD Term.star
      decideIn K (fun Γ ↦ apps equalT [key Γ, child0 (hd Γ)])
        rest (linkK K "atIndexMap: the head" byNormS) Γ₁ Φ₁ ψ₁
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The memberships of a node's children as the memberships' fold writes them, in the context of
the children v0, the markers v1 and the label v2, its rules: the first application of a map over
the children in the normal form of the memberships at the node, the memberships unfolded. -/
def kidsFold (K : Kit) : Option Term := do
  let P := K.P
  let Γ := [list treeTy, list treeTy, bitsTy]
  let (mem, _) ← evalRw K.G K.E (K.rules [] ++ [.delta (P.idx "Typing.memberships")]) .full Γ []
    (pc P "Typing.memberships" [v 1, nodeT (Term.pair (v 2) (v 0))])
  -- the map, beneath binders where the children are the variable of index j, its free
  -- variables lowered by j
  let found := RoseTree.para (fun l (cs : List (Term × Option Term)) ↦
    match cs.findSome? (·.2) with
    | some r => some r
    | none =>
      let u : Term := RoseTree.node l (cs.map Prod.fst)
      match u.label, u.children with
      | .app, [f, _] => match f.label, f.children with
        | .listRec, [_, _, inner] => match inner.label, inner.children with
          | .listRec, [_, _, xs] => match xs.label with
            | .var j => some (Term.subst u fun i ↦ v (i - j))
            | _ => none
          | _, _ => none
        | _, _ => none
      | _, _ => none) mem
  match found with
  | some r => some r
  | none => dbgTrace "kidsFold: none" fun _ ↦ none

/-- The memberships of a node's children as the memberships' fold writes them ({name}`kidsFold`)
are the map of the memberships over the children ({name}`childMemberships`): by induction on the
children, both by normalization with the memberships unfolded. In the context of the children,
the markers and the label. -/
def kidsMemberships (P : Prog) (S : Defs) : Step :=
  ("kidsMemberships", fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, []⟩
    let unfold : List Internal.NormRule := [.delta (P.idx "Typing.memberships")]
    let some rs := kidsFold K | dbgTrace "kidsMemberships: no fold" fun _ ↦ none
    let rhs := mapListsT (Term.lam treeTy (pc P "Typing.memberships" [v 2, v 0])) (v 0)
    let φ := Term.eq rs rhs
    let byU : Deducer := fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let d₀ ← linkK K "kidsMemberships: empty" byU [list treeTy, bitsTy] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let d₁ ← linkK K "kidsMemberships: a construction" (fun Γ Φ ψ ↦
        -- the induction hypothesis of index 0 supplies no rule: cut in again
        dCut (Φ.getD 0 Term.star) (nd (.hyp 0)) byU Γ Φ ψ)
      [list treeTy, treeTy, list treeTy, bitsTy] [Internal.weakenElem φ]
      (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy, list treeTy, bitsTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The constructors of a datatype's marker, as the typing reads them
({lit}`Typing.markerCtors`). -/
def specsOf (P : Prog) (ms dt : Term) : Term :=
  Term.snd (pc P "Typing.markerCtors" [ms, dt])

/-- A member of a datatype passes the test of one of its marker's constructors
({name}`specsOf`) at its label and its children's memberships. In the context of the tree, the
datatype and the markers. Proved by the tree's node: the index of the datatype among the markers'
names decided, absent refuting the membership; present, the memberships at the node unfolded, a
map over the markers, whose element at the index is the marker's ({name}`atIndexMap`). -/
def memberCtors (P : Prog) (S : Defs) : Step :=
  ("memberCtors", fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, []⟩
    let o := P.o
    let Γ := [treeTy, treeTy, list treeTy]
    let (t, dt, ms) := (v 0, v 1, v 2)
    let member := truth o (pc P "Typing.memberOf" [ms, dt, t])
    let goal := truth o (anyT P (pc P "Typing.ctorOk" [sh 2 ms, v 1, labT (v 2),
      childMemberships P (sh 2 ms) (v 2)]) (specsOf P ms dt))
    let a : Internal.Thm := ⟨0, Γ, [member], goal⟩
    let unfold : List Internal.NormRule := [.delta (P.idx "Typing.memberships")]
    -- the memberships' element at a marker, as their fold writes it at a node of label l and
    -- children kids
    let some d := (K.treeNode t <| normLastK K fun Γ Φ ψ ↦
        -- the node's label and children, at fixed positions
        let (pL, pK) := (Γ.length - 2, Γ.length - 1)
        let idx (Γ : List Tree) : Term := markerIdx P (atPos 1 Γ) (atPos 0 Γ)
        -- the memberships' element at a marker, read off their fold's step at the node: the
        -- head of the step at the marker and the empty list
        let g (Γ : List Tree) (Φ : List Term) : Term :=
          let mem := ((evalRw K.G K.E (K.rules Φ ++ unfold) .full Γ Φ
            (pc P "Typing.memberships" [atPos 0 Γ, atPos 2 Γ])).map Prod.fst).getD Term.star
          match findFoldr (atPos 0 Γ) mem with
          | some f => match foldrParts f with
            | some (_, step, _) => Term.lam treeTy
                (headT (Term.app (Term.app (sh 1 step) (v 0)) (nilT treeTy)))
            | none => dbgTrace "memberCtors: no step" fun _ ↦ Term.star
          | none => dbgTrace "memberCtors: no fold" fun _ ↦ Term.star
        decideIn K (fun Γ ↦ pc P "Prelude.isSome" [idx Γ])
          (linkK K "memberCtors: no marker" fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ unfold) .full) 0 (dFalse K.L dHyp) Γ Φ ψ)
          -- the children's memberships as the fold writes them, the map, before the element
          -- function is read off the fold
          (K.cutThm "kidsMemberships" (fun Γ ↦ [atPos pK Γ, atPos 0 Γ, atPos pL Γ]) <|
            normLastK K <|
            K.cutThm "atIndexMap" (fun Γ ↦ [atPos 0 Γ]) <|
            (fun k Γ Φ ψ ↦ dAllE K.L K.G K.E (Φ.length - 1) (g Γ Φ) k Γ Φ ψ) <|
            K.allEΓ (atPos 1) <|
            K.impE (linkK K "memberCtors: the index" (K.solve 3)) <| normLastK K <|
            linkK K "memberCtors: the membership" fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ unfold) .full) 0
                (dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold) .full) dHyp) Γ Φ ψ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "memberCtors: not proved" fun _ ↦ none
    pure (a, d))

/-- The goal by k, else decided by case analysis of a bit or bitstring a fold or a conditional in
its normal form is blocked on, outside binders, the innermost first, to a depth, each case by k:
the goal's {name}`Kit.splitHyp`. -/
def splitGoal (K : Kit) (k : Deducer) (depth : ℕ := 6) : Deducer := (Nat.rec
  (motive := fun _ ↦ Deducer) k
  (fun _ rec Γ Φ ψ ↦ (k Γ Φ ψ).orElse fun _ ↦ do
    -- the scrutinees of the folds anywhere in the goal's normal form, the innermost first
    let (t, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ ψ
    let scr : List Term := RoseTree.para (fun l (cs : List (Term × List Term)) ↦
      let below := cs.flatMap (·.2)
      match l, cs with
      | .lam _, _ => []
      | .listRec, [_, _, (d, _)] => below ++ [d]
      | .app, [(f, _), (x, _)] => match f.label with
        | .arr 5 _ => below ++ [x]
        | _ => below
      | _, _ => below) t
    let some X := scr.find? fun X ↦
        let ty := Internal.typeIn K.G 0 Γ X
        ty = some bitsTy ∨ ty = some bitTy
      | none
    if Internal.typeIn K.G 0 Γ X = some bitTy then K.bitCase X rec rec Γ Φ ψ
    else K.listCase bitTy X rec rec Γ Φ ψ) depth)

/-- The erasure of a list node is named by no keyword, its representation no atom: its step
unfolded once
({name}`eraseHead`), the list split, at a construction the step's tests decided, each branch a
list, the binding's builder unfolded. In the context of the list and the keyword. -/
def eraseListNotAtom (P : Prog) (S : Defs) : Step :=
  ("eraseListNotAtom", fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let Γ := [treeTy, list treeTy]
    let er (t : Term) : Term := pc P "Datatype.eraseExpr" [t]
    let a : Internal.Thm := ⟨0, Γ, [],
      Term.eq (pc P "Datatype.namedTx" [er (pc P "Typing.tList" [v 1]), v 0]) (leafT bnilT)⟩
    -- the binding's builder unfolded
    let byNorm' : Deducer := fun Γ Φ ψ ↦ dEq (fun Γ Φ t u ↦
      let rs := K.rules Φ ++ [.delta (P.idx "Datatype.sLet")]
      byMode .full K.G K.E 0 rs Γ (rwHyps rs Φ) t u) Γ Φ ψ
    -- the erasure's forced children, the step's tests at their head decided, each with its
    -- length's test
    let fm ← forcedMapOf K Γ (v 1)
    let named (kw : String) (n : ℕ) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Datatype.namedTx" [pc P "Datatype.nthTx"
          [sh (Γ.length - 2) fm, leafT (numeral 0)], pc P kw []]) k
        (decideIn K (fun Γ ↦ eqL (pc P "Prelude.length" [sh (Γ.length - 2) fm])
          (leafT (numeral n))) k k)
    let some d := (fun Γ Φ ψ ↦ K.listCase treeTy (atPos 0 Γ)
        (K.cutThm "eraseHead" (fun _ ↦ [nilT treeTy]) <| normLastK K <|
          linkK K "eraseListNotAtom: empty" K.byNorm)
        (fun Γ Φ ψ ↦
          let lst := consT treeTy (atPos (Γ.length - 2) Γ) (atPos (Γ.length - 1) Γ)
          (K.cutThm "eraseHead" (fun _ ↦ [lst]) <| normLastK K <|
            named "Typing.kwRep" 2 <| named "Typing.kwDecode" 5 <| named "Typing.kwDatum" 3 <|
            linkK K "eraseListNotAtom: a construction" (splitGoal K byNorm')) Γ Φ ψ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "eraseListNotAtom: not proved" fun _ ↦ none
    pure (a, d))

/-- The elements of the erasure of the list node of clauses' metadata, each a list, are the
erasure's forced map of the metadata ({name}`forcedMapOf`): its step unfolded once
({name}`eraseHead`), the list split; at a construction, the head's node a list's, else the
hypothesis refuted, whose erasure no keyword names ({name}`eraseListNotAtom`). In the context of
the metadata. -/
def eraseMetas (P : Prog) (S : Defs) : Step :=
  ("eraseMetas", fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let Γ := [list treeTy]
    let er (t : Term) : Term := pc P "Datatype.eraseExpr" [t]
    let fm ← forcedMapOf K Γ (v 0)
    let isList := Term.lam treeTy (truth P.o (pc P "Datatype.isListTx" [v 0]))
    let a : Internal.Thm := ⟨0, Γ, [S.allL isList (v 0)],
      Term.eq (pc P "Datatype.elems" [er (pc P "Typing.tList" [v 0])]) fm⟩
    let byNorm' : Deducer := fun Γ Φ ψ ↦ dEq (fun Γ Φ t u ↦
      let rs := K.rules Φ ++ [.delta (P.idx "Datatype.sLet")]
      byMode .full K.G K.E 0 rs Γ (rwHyps rs Φ) t u) Γ Φ ψ
    let notNamed (kw : String) (pk : ℕ) (k : Deducer) : Deducer :=
      K.cutThm "eraseListNotAtom" (fun Γ ↦ [pc P kw [], atPos pk Γ]) <| normLastK K k
    let some d := (fun Γ Φ ψ ↦ K.listCase treeTy (atPos 0 Γ)
        (K.cutThm "eraseHead" (fun _ ↦ [nilT treeTy]) <| normLastK K <|
          linkK K "eraseMetas: empty" byNorm')
        (fun Γ Φ ψ ↦
          let (pm, pr) := (Γ.length - 2, Γ.length - 1)
          let lst := consT treeTy (atPos pm Γ) (atPos pr Γ)
          -- the head's shape a hypothesis
          (dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 <| K.conjE fun Γ Φ ψ ↦
          let hL := Φ.length - 2
          (linkK K "eraseMetas: the head's node" <| K.treeNode (atPos pm Γ)
            (normLastK K fun Γ Φ ψ ↦
              let pk := Γ.length - 1
              dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
                if bs.map Oitavem.rank == some 2 then
                  K.cutThm "eraseHead" (fun Γ ↦ [lst.rename fun i ↦ i + (Γ.length - 3)]) <|
                    normLastK K <| notNamed "Typing.kwRep" pk <|
                    notNamed "Typing.kwDecode" pk <| notNamed "Typing.kwDatum" pk <|
                    linkK K "eraseMetas: a construction" (splitGoal K byNorm')
                else linkK K s!"eraseMetas: the head's label {bs.map Oitavem.rank}"
                  (K.hypFalse hL))
                3 [] (v 1) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "eraseMetas: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness at case analyses' clauses. -/
def clausesDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [atomExcluded P S "scrutExcluded" (scrutineeName P),
    atomExcluded P S "childrenExcluded" (childrenName P), childrenNums P S T, clauseRes P S T,
    childrenConv P S, clause P S T, condConv P S, clauseAt P S T,
    atomExcluded P S "ifExcluded" (pc P "Reader.kwIf" []),
    atomExcluded P S "eqExcluded" (atomNameT (pc P "Datatype.aEq" [])),
    atomExcluded P S "labelExcluded" (atomNameT (pc P "Datatype.aLabel" []))] ++
  (testAtoms P).map (fun (nm, a) ↦ notNumeral P S nm a) ++
  indexLemmas P S ++ ifEqs P S T ++
  [testNums P S T, testRes P S T, testConv P S, condTyped P S, caseFieldsNothing P S T,
    eraseAtomsMap P S T, eraseAtoms P S T, walkBinders P S T, eraseHead P S, eraseMeta P S T,
    chain P S T, atIndexMap P S, kidsMemberships P S, memberCtors P S, eraseListNotAtom P S,
    eraseMetas P S]

/-- The development of {name}`clausesDev`, after the declarations of {name}`caseNames` and of the
walk's development ({name}`caseDev`), stored as the certificate {lit}`datatype-clauses`. -/
def clausesCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := caseNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (caseDev P S T).map (·.1)) "datatype-clauses" (clausesDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
