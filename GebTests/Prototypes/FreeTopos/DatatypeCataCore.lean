/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeCataSound
public meta import GebTests.Prototypes.FreeTopos.DatatypeCataSound -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at an expanded structural recursion

The soundness of the datatype language's stage-1 compiler at an expanded structural recursion: its
resolved term's kernel's typing and its convergence, from the chain of its clauses and the fold's
convergence at every tree.

## Main definitions

* {lit}`cataCoreCertificates` — the development, stored as the certificate
  {lit}`datatype-cata-core`.

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

/-- The kernel's terms of a structural recursion's resolution, read off the right side of
{name}`cataResEq`, in its context: the fold's constant, the abstractions' types, the chain, the
scrutinee and the unit value. -/
structure CataTerms where
  /-- The fold's constant at its type. -/
  c : Term
  /-- The type of the node's abstraction. -/
  tO : Term
  /-- The type of the suspended results' abstraction. -/
  tK : Term
  /-- The type of the unit's abstraction. -/
  tU : Term
  /-- The chain's term. -/
  ch : Term
  /-- The scrutinee's term. -/
  s : Term
  /-- The unit value's term. -/
  u : Term

/-- The kernel's terms of a structural recursion's resolution ({name}`CataTerms`). -/
def cataTerms (E : Array Internal.Entry) (ix : String → ℕ) : Option CataTerms := do
  let y ← boundTerm E ix "cataResEq"
  let [f0, u] ← nodeKidsT y | none
  let [f1, s] ← nodeKidsT f0 | none
  let [c, st] ← nodeKidsT f1 | none
  let [tO, lK] ← nodeKidsT st | none
  let [tK, lU] ← nodeKidsT lK | none
  let [tU, ch] ← nodeKidsT lU | none
  pure ⟨c, tO, tK, tU, ch, s, u⟩

namespace CataTerms

variable (t : CataTerms)

/-- The step's term. -/
def step : Term := lamT t.tO (lamT t.tK (lamT t.tU t.ch))

/-- The fold's term at the scrutinee, a suspended result. -/
def fold : Term := appT (appT t.c t.step) t.s

/-- The resolved term. -/
def whole : Term := appT t.fold t.u

/-- The terms at the instance {lit}`σ` of the context of {name}`cataResEq`. -/
def inst (σ : List Term) : CataTerms :=
  let i := Internal.instTerm [] σ
  ⟨i t.c, i t.tO, i t.tK, i t.tU, i t.ch, i t.s, i t.u⟩

end CataTerms

/-- The statement that the kernel types a term in a context, at the globals' types {lit}`G`. -/
def checkTypedAt (P : Prog) (G ctx t : Term) : Term :=
  truth P.o (pc P "Prelude.isSome" [pc P "Check.typeIn" [G, ctx, t]])

/-- The kernel's typing of an application at its parts: where the kernel types it, it types the
function and the argument. In the context of the argument, the function, the kernel's context and
the globals' types. Each part's type decided, absent refuting the hypothesis. -/
def appTyped (P : Prog) (S : Defs) : Step :=
  ("appTyped", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let a : Internal.Thm := ⟨0, [treeTy, treeTy, list treeTy, list treeTy],
      [checkTypedAt P (v 3) (v 2) (appT (v 1) (v 0))],
      Internal.Logic.conj P.o (checkTypedAt P (v 3) (v 2) (v 1)) (checkTypedAt P (v 3) (v 2) (v 0))⟩
    let (x, f, C, G) := (atPos 3, atPos 2, atPos 1, atPos 0)
    let refute (msg : String) : Deducer := linkK K s!"appTyped: {msg}" (K.hypFalse 0)
    let typeIn (t : List Tree → Term) (Γ : List Tree) : Term := pc P "Check.typeIn" [G Γ, C Γ, t Γ]
    let some d := (decideOpt K (typeIn f) (refute "the function untyped") <|
        decideOpt K (typeIn x) (refute "the argument untyped") <|
        linkK K "appTyped: the parts" (dConjI K.L (K.solve 3) (K.solve 3)))
        a.ctx a.hyps a.concl
      | dbgTrace "appTyped: not proved" fun _ ↦ none
    pure (a, d))

/-- The kernel's typing of an abstraction at its body: where the kernel types it, it types the body
in the context extended by the type. In the context of the body, the type, the kernel's context and
the globals' types. The type's being a type decided, then the body's type, each absent refuting the
hypothesis. -/
def lamTyped (P : Prog) (S : Defs) : Step :=
  ("lamTyped", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let a : Internal.Thm := ⟨0, [treeTy, treeTy, list treeTy, list treeTy],
      [checkTypedAt P (v 3) (v 2) (lamT (v 1) (v 0))],
      checkTypedAt P (v 3) (consT treeTy (v 1) (v 2)) (v 0)⟩
    let (b, A, C, G) := (atPos 3, atPos 2, atPos 1, atPos 0)
    let refute (msg : String) : Deducer := linkK K s!"lamTyped: {msg}" (K.hypFalse 0)
    let some d := (decideIn K (fun Γ ↦ pc P "Check.isTy" [A Γ]) (refute "not a type") <|
        decideOpt K (fun Γ ↦ pc P "Check.typeIn" [G Γ, consT treeTy (A Γ) (C Γ), b Γ])
          (refute "the body untyped") <|
        linkK K "lamTyped: the body" (K.solve 3))
        a.ctx a.hyps a.concl
      | dbgTrace "lamTyped: not proved" fun _ ↦ none
    pure (a, d))

/-- The kernel's typing of a structural recursion's resolved term at its parts: where the kernel
types the whole, it types the chain in the kernel's context extended by the abstractions' types and
the scrutinee in the kernel's context: {name}`appTyped` and {name}`lamTyped`, from the outside in.
In the context of {name}`cataResEq`, the kernel's context and the globals' types. -/
def cataTyped (P : Prog) (S : Defs) : Step :=
  ("cataTyped", fun ix E ↦ do
    let P := { walkProg P with folded := (walkProg P).folded ++ ["Check.typeIn"] }
    let K : Kit := ⟨P, S, E, ix, []⟩
    let t ← cataTerms E ix
    let L := list treeTy
    let Γ := [treeTy, treeTy, treeTy, L, L, L, L, L]
    let (kc, G) := (v 6, v 7)
    let kcO := consT treeTy t.tO kc
    let kcK := consT treeTy t.tK kcO
    let kcU := consT treeTy t.tU kcK
    let a : Internal.Thm := ⟨0, Γ, [checkTypedAt P G kc t.whole],
      Internal.Logic.conj P.o (checkTypedAt P G kcU t.ch) (checkTypedAt P G kc t.s)⟩
    let at_ (u : Term) (Δ : List Tree) : Term := sh (Δ.length - Γ.length) u
    let lamK := lamT t.tK (lamT t.tU t.ch)
    let lamU := lamT t.tU t.ch
    let byLast2 : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let some d := (applyThm K "appTyped" (fun Δ ↦ [at_ t.u Δ, at_ t.fold Δ, at_ kc Δ, at_ G Δ])
        [K.byHyp 0] <| K.conjE <|
      applyThm K "appTyped" (fun Δ ↦ [at_ t.s Δ, at_ (appT t.c t.step) Δ, at_ kc Δ, at_ G Δ])
        [byLast2] <| K.conjE fun Γ₁ Φ₁ ψ₁ ↦
      let (iF, iS) := (Φ₁.length - 2, Φ₁.length - 1)
      (applyThm K "appTyped" (fun Δ ↦ [at_ t.step Δ, at_ t.c Δ, at_ kc Δ, at_ G Δ]) [K.byHyp iF] <|
        K.conjE <|
      applyThm K "lamTyped" (fun Δ ↦ [at_ lamK Δ, at_ t.tO Δ, at_ kc Δ, at_ G Δ]) [byLast] <|
      applyThm K "lamTyped" (fun Δ ↦ [at_ lamU Δ, at_ t.tK Δ, at_ kcO Δ, at_ G Δ]) [byLast] <|
      applyThm K "lamTyped" (fun Δ ↦ [at_ t.ch Δ, at_ t.tU Δ, at_ kcK Δ, at_ G Δ]) [byLast] <|
      linkK K "cataTyped: the parts" (dConjI K.L byLast (K.byHyp iS))) Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "cataTyped: not proved" fun _ ↦ none
    pure (a, d))

/-- The chain's fact at a structural recursion's step: at every tree, results and unit value, the
results as many as the tree's children and related to them and the tree's memberships passing the
test of a field of the datatype, the chain's term {lit}`ch` converges, in the environment of the
unit value, the results' list value and the tree's quotation before {lit}`env`, to a value related
at the result type. -/
def chainFact (P : Prog) (S : Defs) (T : Defs3) (ch env A R Dc d E : Term) : Term :=
  let imp := Internal.Logic.imp P.o
  let all (B : Tree) (t : Term) : Term := Internal.Logic.all P.o B (Term.lam B t)
  let ms := pc P "Typing.envMs" [sh 3 E]
  -- beneath the three quantifiers: the unit value v0, the results v1 and the tree v2
  let ts := call D.children [] [v 2]
  let env' := consT treeTy (v 0) (consT treeTy (pc P "Eval.ofList" [sh 3 A, v 1])
    (consT treeTy (pc P "Eval.valQuote" [v 2]) (sh 3 env)))
  all treeTy <| all (list treeTy) <| all treeTy <|
    imp (lenEqT P ts (v 1)) <| imp (relatedT P T (sh 3 E) (sh 3 d) (sh 3 Dc) (sh 3 R) ts (v 1)) <|
    imp (truth P.o (pc P "Typing.fieldOk" [ms, sh 3 d, pc P "Typing.memberships" [ms, v 2]])) <|
    S.conv (Term.lam nat (S.evN (Term.fst (sh 4 Dc)) (v 0) (sh 1 env') (sh 4 ch)))
      (T.relT (sh 3 Dc) (sh 3 R))

/-- The step's value, the closure of a structural recursion's step in an environment, satisfies the
fold's hypothesis ({name}`paraStepH`), given the chain's fact ({name}`chainFact`): its applications
to a tree's quotation and to the results' list value converge at once to the closure of the unit's
abstraction, which, the tests holding, the relation at the arrow's type unfolded ({lit}`relTArrow`),
applied to a value converges as the chain does, a level below. In the context of the chain's term,
the abstractions' types and bodies, the environment, the carried type, the result type, the
relation's context, the datatype and the typing environment. -/
def cataStepOk (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cataStepOk", fun ix E ↦ do
    let P := { walkProg P with folded := (walkProg P).folded ++ ["Check.typeIn"] }
    let K : Kit := ⟨P, S, E, ix, evalMore ++ ["relTArrow", "nthOne2", "nthOne3"]⟩
    let L := K.L
    let Lt := list treeTy
    -- the chain v0, the types tU v1, tK v2, tO v3, the environment v4, the carried type v5, the
    -- result type v6, the relation's context v7, the datatype v8, the typing environment v9
    let Γ := [treeTy, treeTy, treeTy, treeTy, Lt, treeTy, treeTy, Defs3.ctxTy, treeTy, T.envTy]
    let f := pc P "Eval.valClo" [v 4, v 3, lamT (v 2) (lamT (v 1) (v 0))]
    let a : Internal.Thm := ⟨0, Γ,
      [Internal.Logic.tt P.o, chainFact P S T (v 0) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)],
      paraStepH P S T f (v 5) (v 6) (v 7) (v 8) (v 9)⟩
    let at_ (i : ℕ) (Δ : List Tree) : Term := v (Δ.length - Γ.length + i)
    let lv : Term := (5 : ℕ).rec zeroN fun _ t ↦ succN t
    let some d := (dAllI L <| dAllI L fun Γ₁ Φ₁ ψ₁ ↦
        let (t, rs) := (v 1, v 0)
        let w₁ (Δ : List Tree) : Term := sh (Δ.length - Γ₁.length)
          (pc P "Eval.valClo" [consT treeTy (pc P "Eval.ofList" [at_ 5 Γ₁, rs])
            (consT treeTy (pc P "Eval.valQuote" [t]) (at_ 4 Γ₁)), at_ 1 Γ₁, at_ 0 Γ₁])
        K.conv (fun _ ↦ lv) w₁ (linkK K "cataStepOk: stable" K.byNorm)
          (linkK K "cataStepOk: related" <| K.norm <| dImpI L <| dImpI L <| dImpI L
            fun Γ₂ Φ₂ ψ₂ ↦
            let (iLen, iRel, iMem) := (Φ₂.length - 3, Φ₂.length - 2, Φ₂.length - 1)
            (linkK K "cataStepOk: the arrow" <| K.norm <| dAllI L <| dImpI L fun Γ₃ Φ₃ ψ₃ ↦
              dAllE L K.G K.E 1 (sh (Γ₃.length - Γ₁.length) t) (K.allEΓ (fun Δ ↦
                sh (Δ.length - Γ₁.length) rs) <| K.allEΓ (fun Δ ↦ v (Δ.length - Γ₃.length)) <|
                K.impE (K.byHyp iLen) <| K.impE (K.byHyp iRel) <| K.impE (K.byHyp iMem) <|
                K.unfoldConv <| K.exE <| K.exE <| K.conjE fun Γ Φ ψ ↦
                  dConv L K.G K.E S (succN (v 1)) (v 0)
                    (linkK K "cataStepOk: applied stable" <|
                      instNK K (Φ.length - 2) (fun _ ↦ v 0) K.byNorm)
                    (linkK K "cataStepOk: applied related" (K.byHyp (Φ.length - 1))) Γ Φ ψ)
                Γ₃ Φ₃ ψ₃) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "cataStepOk: not proved" fun _ ↦ none
    pure (a, d))

/-- The convergence of a structural recursion's fold at a scrutinee: where the chain's fact holds
({name}`chainFact`), the scrutinee's term converges to a tree's quotation and the tree's memberships
pass the test of a field of the datatype, the resolved term converges to a value related at the
result type: the fold's value at the tree ({name}`cataPara`), at the step's closure
({name}`cataStepOk`), a suspended result related; its application to the unit value
({lit}`appCompat`). In the context of {name}`cataResEq`, the environment, the tree, the result type,
the relation's context, the datatype and the typing environment. -/
def cataConv (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cataConv", fun ix E ↦ do
    let P := { walkProg P with folded := (walkProg P).folded ++ ["Check.typeIn"] }
    let K : Kit := ⟨P, S, E, ix, (evalMore ++ apNames "apPara" 2 ++ ["relTArrow"]).eraseDups⟩
    let L := K.L
    let Lt := list treeTy
    let t ← cataTerms E ix
    let [A] ← nodeKidsT t.c | dbgTrace "cataConv: the constant" fun _ ↦ none
    -- the context of the resolution v0 to v5, then the environment v6, the tree v7, the result
    -- type v8, the relation's context v9, the datatype v10 and the typing environment v11
    let Γ := [treeTy, treeTy, treeTy, Lt, Lt, Lt, Lt, treeTy, treeTy, Defs3.ctxTy, treeTy, T.envTy]
    let (env, tr, Rt, Dv, dt, Ee) := (v 6, v 7, v 8, v 9, v 10, v 11)
    let ms := pc P "Typing.envMs" [Ee]
    let quote := pc P "Eval.valQuote" [tr]
    let a : Internal.Thm := ⟨0, Γ, [Internal.Logic.tt P.o,
        chainFact P S T t.ch env A Rt Dv dt Ee,
        S.conv (Term.lam nat (S.evN (Term.fst (sh 1 Dv)) (v 0) (sh 1 env) (sh 1 t.s)))
          (Term.lam treeTy (Term.eq (v 0) (sh 1 quote))),
        truth P.o (pc P "Typing.fieldOk" [ms, dt, pc P "Typing.memberships" [ms, tr]])],
      S.conv (Term.lam nat (S.evN (Term.fst (sh 1 Dv)) (v 0) (sh 1 env) (sh 1 t.whole)))
        (T.relT Dv Rt)⟩
    let at_ (u : Term) (Δ : List Tree) : Term := sh (Δ.length - Γ.length) u
    let f := pc P "Eval.valClo" [env, t.tO, lamT t.tK (lamT t.tU t.ch)]
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let unitTy := pc P "Typing.tyUnit" []
    let [fold, u] ← nodeKidsT t.whole | none
    let lv1 : Term := succN (succN (succN zeroN))
    let unitOk : Deducer := fun Γ Φ ψ ↦
      dConv L K.G K.E S lv1 (nodeT (Term.pair (numeral Kernel.Label.unit) (nilT treeTy)))
        (linkK K "cataConv: unit stable" K.byNorm)
        (linkK K "cataConv: unit related" fun Γ Φ ψ ↦
          dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta T.q]) .full) (K.solve 3) Γ Φ ψ) Γ Φ ψ
    -- the fold's convergence: the thresholds of the fold's value and of the scrutinee shifted to
    -- their sum, three levels above which the application of the constant to the step and the
    -- scrutinee evaluates to the fold's value
    let some d := (applyThm K "cataStepOk" (fun Δ ↦ [at_ t.ch Δ, at_ t.tU Δ, at_ t.tK Δ,
          at_ t.tO Δ, at_ env Δ, at_ A Δ, at_ Rt Δ, at_ Dv Δ, at_ dt Δ, at_ Ee Δ])
        [K.solve 3, K.byHyp 1] fun Γ₀ Φ₀ ψ₀ ↦
      let iH := Φ₀.length - 1
      (K.cutThm "cataPara" (fun Δ ↦ [at_ tr Δ]) <|
        allEs K (Φ₀.length) [at_ Ee, at_ dt, at_ Dv, at_ Rt, at_ A, at_ f] <|
        K.impE (linkK K "cataConv: the step" (K.byHyp iH)) <|
        K.convE fun Γ₁ Φ₁ ψ₁ ↦
        let n₁ (Δ : List Tree) : Term := v (Δ.length - Γ₁.length + 1)
        let w (Δ : List Tree) : Term := v (Δ.length - Γ₁.length)
        let (s₁, r₁) := (Φ₁.length - 2, Φ₁.length - 1)
        (normHyps K [r₁] <| fun Γ Φ ψ ↦ dImpE L (Φ.length - 1)
          (linkK K "cataConv: the member" (K.byHyp 3)) (fun Γ Φ ψ ↦
          let iRel := Φ.length - 1
          dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) 2 (K.exE <| K.exE <| K.conjE
            fun Γ₂ Φ₂ ψ₂ ↦
            let n₂ (Δ : List Tree) : Term := v (Δ.length - Γ₂.length + 1)
            let (s₂, r₂) := (Φ₂.length - 2, Φ₂.length - 1)
            (normHyps K [r₂] <| K.shift s₁ false n₂ <| K.shift s₂ true n₁ fun Γ Φ ψ ↦
              let (a₁, a₂) := (Φ.length - 2, Φ.length - 1)
              let sum (Δ : List Tree) : Term := S.add (n₁ Δ) (n₂ Δ)
              (K.cutThm "appCompat" (fun Δ ↦ [at_ env Δ, at_ u Δ, at_ fold Δ, at_ Rt Δ, unitTy,
                  at_ Dv Δ]) <|
                K.impE (linkK K "cataConv: the fold" fun Γ Φ ψ ↦
                  K.conv (fun Δ ↦ succN (succN (succN (sum Δ)))) w
                    (linkK K "cataConv: the fold stable" fun Γs Φs ψs ↦
                      let m (Δ : List Tree) : Term := v (Δ.length - Γs.length)
                      (generalizeK K (at_ f) <|
                      K.instN a₁ (fun Δ ↦ succN (m Δ)) <|
                      K.instN a₂ (fun Δ ↦ succN (succN (succN (m Δ)))) K.byNorm) Γs Φs ψs)
                    (linkK K "cataConv: the fold related" (K.byHyp iRel)) Γ Φ ψ) <|
                K.impE (linkK K "cataConv: the unit" unitOk) <|
                linkK K "cataConv: the conclusion" byLast) Γ Φ ψ) Γ₂ Φ₂ ψ₂) Γ Φ ψ) Γ Φ ψ)
          Γ₁ Φ₁ ψ₁) Γ₀ Φ₀ ψ₀)
        a.ctx a.hyps a.concl
      | dbgTrace "cataConv: not proved" fun _ ↦ none
    pure (a, d))

/-- Each entry of a list node that is a source form has its variable's characters fixed
({name}`fixedEntry`): by induction on the entries, the test of source forms split at the head
({lit}`srcCons`); the head's variable an atom only where the head is a list with a first element,
whose test, the source forms' step unfolded, is its characters'. In the context of the entries and
the numeral abbreviations. -/
def entriesFixed (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("entriesFixed", fun ix E ↦ do
    let K : Kit := ⟨walkProg P, S, E, ix, (vocab3 ++ ["srcCons"]).filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size⟩
    let L := K.L
    let P := K.P
    let φ := Internal.Logic.imp P.o (srcAt P (v 1) (pc P "Typing.tList" [v 0]))
      (S.allL (fixedEntry P (v 1)) (v 0))
    let Γ := [list treeTy, list treeTy]
    let d₀ ← dImpI L (K.solve 3) Γ.tail [] (Term.subst φ (Internal.instVar (nilT treeTy)))
    let srcT (x : Term) (Γ : List Tree) : Term :=
      pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [sh 1 (atPos 0 Γ), v 0]), x]
    let unfoldS : List Internal.NormRule := [.delta (T.argIdx 5)]
    let anyFalse' : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.hypFalse h Γ Φ ψ
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let nodeOf (x : List Tree → Term) (r : ℕ) (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
      K.treeNode (x Γ) (normLastK K fun Γ Φ ψ ↦
        let pk := Γ.length - 1
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          if bs.map Oitavem.rank == some r then k pk
          else linkK K s!"entriesFixed: the label {bs.map Oitavem.rank}" anyFalse')
          3 [] (v 1) Γ Φ ψ) Γ Φ ψ
    -- the test of source forms at the head's elements, the step unfolded, split at its first
    let elementTest (iX pk : ℕ) : Deducer := fun Γ Φ ψ ↦
      K.listCase treeTy (atPos pk Γ) (linkK K "entriesFixed: no element" anyFalse') (fun Γ Φ ψ ↦
        let (px, pr) := (Γ.length - 2, Γ.length - 1)
        (applyThm K "andParts" (fun Γ ↦ [srcT (pc P "Typing.tList" [atPos pr Γ]) Γ,
            srcT (atPos px Γ) Γ])
          [linkK K "entriesFixed: the elements' test" fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ iX ++ unfoldS) .full) iX
              (dRwBy (evalRw K.G K.E (K.rules Φ ++ unfoldS) .full) dHyp) Γ Φ ψ] <|
          K.conjE fun Γ Φ ψ ↦
          let iV := Φ.length - 2
          nodeOf (atPos px) 1 (fun _ ↦ linkK K "entriesFixed: an atom" fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ iV ++ unfoldS) .full) iV byLast Γ Φ ψ) Γ Φ ψ)
          Γ Φ ψ) Γ Φ ψ
    let cons : Deducer := dImpI L fun Γ Φ ψ ↦
      let iS := Φ.length - 1
      let (pe, pr) := (Γ.length - 2, Γ.length - 1)
      let head (iX : ℕ) : Deducer := linkK K "entriesFixed: the head" <| dImpI L <|
        nodeOf (atPos pe) 2 (elementTest iX)
      let rest (iR : ℕ) : Deducer := linkK K "entriesFixed: the rest" <|
        dImpE L 0 (K.byHyp iR) byLast
      (applyThm K "andParts" (fun Γ ↦ [srcT (pc P "Typing.tList" [atPos pr Γ]) Γ,
          srcT (atPos pe Γ) Γ]) [linkK K "entriesFixed: the test split" (K.byHyp iS)] <|
        K.conjE fun Γ Φ ψ ↦
        let iR := Φ.length - 1
        let either : Deducer := fun Γ Φ ψ ↦ (rest iR Γ Φ ψ).orElse fun _ ↦ head (iR - 1) Γ Φ ψ
        linkK K "entriesFixed: the parts" (K.norm (dConjI L either either)) Γ Φ ψ) Γ Φ ψ
    let some d₁ := linkK K "entriesFixed: a construction" cons (list treeTy :: treeTy :: Γ.tail)
        [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "entriesFixed: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A structural recursion's clause's metadata's shape, as the expansion writes it: a list, whose
second and third elements are lists ({name}`shapeMeta`), its entries' flags numerals' atoms and its
entries without a third element. -/
def cataShape (P : Prog) (S : Defs) : Term :=
  let conj := Internal.Logic.conj P.o
  Term.lam treeTy (conj (Term.app (shapeMeta P) (v 0))
    ((flagHyps P S (v 0) ++ (shapeHyps P S (v 0)).dropLast).foldr conj
      ((shapeHyps P S (v 0)).getLast?.getD Term.star)))

/-- The chain's characters of a structural recursion's clause's metadata fixed, at the numeral
abbreviations {lit}`nums` outside the predicate's binder ({name}`cataChainSpec`). -/
def fixedMetaCata (P : Prog) (S : Defs) (nums : Term) : Term :=
  let conj := Internal.Logic.conj P.o
  let f := fixedEntry P (sh 1 nums)
  let isList (n : ℕ) : Term := truth P.o (pc P "Datatype.isListTx"
    [pc P "Datatype.nthTx" [pc P "Datatype.elems" [v 0], leafT (numeral n)]])
  Term.lam treeTy (conj (S.allL f (metaAt P (v 0) 1)) (conj (S.allL f (metaAt P (v 0) 2))
    ((flagHyps P S (v 0) ++ shapeHyps P S (v 0)).foldr conj
      (conj (Term.app (fixedAtom P (sh 1 nums)) (labelAtom P (v 0)))
        (conj (isList 1) (isList 2))))))

/-- A structural recursion's clauses' metadata's characters fixed ({name}`metasFixedWith`), by the
entries' lemma ({name}`entriesFixed`), each metadata's shape ({name}`cataShape`) split. -/
def cataMetasFixed (P : Prog) (S : Defs) (T : Defs3) : Step :=
  let L : Conn := ⟨P.o, logicBase⟩
  metasFixedWith "cataMetasFixed" "entriesFixed"
    (fun P ↦ Internal.Logic.imp P.o (srcAt P (v 1) (pc P "Typing.tList" [v 0]))
      (Internal.Logic.imp P.o (S.allL (cataShape P S) (v 0))
        (S.allL (fixedMetaCata P S (v 1)) (v 0))))
    (fun k Γ Φ ψ ↦ dConjE L (Φ.length - 2) (fun Γ Φ ψ ↦
      let iF := Φ.length - 1
      dConjE L (Φ.length - 2) (fun Γ Φ ψ ↦ dConjE L (Φ.length - 1) (fun Γ Φ ψ ↦
        dConjE L iF (fun Γ Φ ψ ↦ dConjE L (Φ.length - 1) (fun Γ Φ ψ ↦
          dConjE L (Φ.length - 1) k Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) 12 P S T

/-- The context of the soundness at an expanded structural recursion: the bodies' forms v0, the
clauses' metadata v1, the default's form v2, the scrutinee's form v3, the result type's form v4 and
the datatype's atom v5. -/
def cataCoreCtx : List Tree := [list treeTy, list treeTy, treeTy, treeTy, treeTy, treeTy]

/-- The expanded structural recursion of {name}`cataCoreCtx`, the typing's node of its parts. -/
def cataNode (P : Prog) : Term :=
  pc P "Typing.tCata" [consT treeTy (v 5) (consT treeTy (v 4) (consT treeTy (v 3)
    (consT treeTy (v 2) (consT treeTy (pc P "Typing.tList" [v 1]) (v 0)))))]

/-- The statement of the soundness at an expanded structural recursion ({name}`cataNode`): where it
holds at the scrutinee's form and at each body's and the metadata are shaped as the expansion writes
them ({name}`cataShape`), it holds at the structural recursion. -/
def cataCoreThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  let φ := expandedφ P S T
  ⟨0, cataCoreCtx, [Internal.instTerm [] [v 3] φ, S.allL (Term.lam treeTy φ) (v 0),
    S.allL (cataShape P S) (v 1)], Internal.instTerm [] [cataNode P] φ⟩

/-- The tools of the proofs at an expanded structural recursion: the case analysis's
({name}`caseKit`) at its context, the clause's fields' typing kept folded. -/
def cataKit (P : Prog) (S : Defs) (T : Defs3) (ix : String → ℕ) (E : Array Internal.Entry) :
    KwKit :=
  let P' := { cataChainProg P with
    folded := (cataChainProg P).folded ++ ["Typing.clausesTy", "Datatype.eraseChain"] }
  let W := kwKit P' S T ix E 6 [true, true, true, false, false, false] (expanded := true)
  { W with K := { W.K with more := (W.K.more ++ walkRules ix E ++
    lenRules.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size).eraseDups } }

/-- The soundness at an expanded structural recursion ({name}`cataCoreThm`). -/
def cataCore (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cataCore", fun ix E ↦ do
    let W := cataKit P S T ix E
    let K := W.K
    let L := K.L
    let P := K.P
    let a := cataCoreThm P S T
    let equalT ← primT Kernel.Prim.equal
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let negated : Deducer := dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let (dt, rF, sF, drF, metas, bodiesF) :=
      (atPos 0, atPos 1, atPos 2, atPos 3, atPos 4, atPos 5)
    let (Gv, kcv, Ev, cxv, tysv, numsv, namesv, envv, Dv) := (W.qv 1, W.qv 2, W.qv 4, W.qv 5,
      W.qv 6, W.qv 7, W.qv 8, W.qv 9, W.qv 10)
    let ms (Γ : List Tree) : Term := pc P "Typing.envMs" [Ev Γ]
    let er (t : List Tree → Term) (Γ : List Tree) : Term := pc P "Datatype.eraseExpr" [t Γ]
    -- the typing's parts: the datatype's type pA, the result type pR, the scrutinee's type pB; the
    -- marker's decision hMk; the clauses' typings and the clauses' type's equation
    let typing (k : ℕ → ℕ → ℕ → (List Tree → Term) → ℕ → ℕ → Deducer) : Deducer :=
      fun Γ₀ Φ₀ ψ₀ ↦ do
      let h ← Φ₀[W.hyp 6]?
      let (t, _) ← evalRw K.G K.E (K.rules Φ₀) .full Γ₀ Φ₀ h
      let some args := (appsOf K.G (P.idx "Typing.synCata") t).head?.map spineArgs
        | dbgTrace "cataCore: no typing" fun _ ↦ none
      let arg (i : ℕ) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) (args.getD i Term.star)
      let (Ev', rs, cx) := (arg 0, arg 2, arg 3)
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₀ (W.hyp 6) ++ [.delta (P.idx "Typing.synCata")]) .full)
        (W.hyp 6) (fun Γ₁ Φ₁ ψ₁ ↦
        let hT := Φ₁.length - 1
        let pres (msg : String) (opt : List Tree → Term) (k : ℕ → Deducer) : Deducer :=
          W.presentAt msg opt hT (W.hyp 6) (fun Γ Φ ψ ↦ k (Γ.length - 1) Γ Φ ψ)
            (unfolding := false)
        let refute (msg : String) : Deducer := linkK K s!"cataCore: {msg}" fun Γ Φ ψ ↦
          (K.hypFalse hT Γ Φ ψ).orElse fun _ ↦ K.hypFalse (W.hyp 6) Γ Φ ψ
        let mc (Γ : List Tree) : Term := pc P "Typing.markerCtors" [pc P "Typing.envMs" [Ev' Γ],
          dt Γ]
        (pres "the datatype's type" (fun Γ ↦ pc P "Typing.readTy" [Ev' Γ, dt Γ]) fun pA ↦
        pres "the result type" (fun Γ ↦ pc P "Typing.readTy" [Ev' Γ, rF Γ]) fun pR ↦
        pres "the scrutinee's type" (fun Γ ↦ pc P "Typing.srAt" [rs Γ, leafT (numeral 2), cx Γ])
          fun pB ↦
        let markers (k : ℕ → Deducer) : Deducer :=
          decideIn K (fun Γ ↦ Term.fst (mc Γ)) (refute "no marker's constructors") <| fun Γ Φ ψ ↦
          let hMk := Φ.length - 1
          decideIn K (fun Γ ↦ pc P "Typing.namesData" [Ev' Γ, atPos pA Γ, dt Γ])
            (refute "the datatype not named") (k hMk) Γ Φ ψ
        decideIn K (fun Γ ↦ apps equalT [atPos pA Γ, atPos pB Γ])
          (markers fun _ ↦ refute "the scrutinee's type another") <|
        linkK K "cataCore: the types' equation" (
        K.cutThm "equalSound" (fun Γ ↦ [atPos pA Γ]) <| K.allEΓ (atPos pB) <|
        K.impE (linkK K "cataCore: the types equal" (K.solve 3)) <| normLastK K <|
        K.cutThm "equalRefl" (fun Γ ↦ [atPos pB Γ]) <|
        decideIn K (fun Γ ↦ apps equalT [atPos pB Γ, atPos pB Γ]) (anyFalse K) <|
        markers fun hMk Γ₂ Φ₂ ψ₂ ↦ do
        let (t₂, _) ← evalRw K.G K.E (K.rules Φ₂) .full Γ₂ Φ₂ (← Φ₂[hT]?)
        let some c := (appsOf K.G (P.idx "Typing.clausesTy") t₂).head?
          | dbgTrace "cataCore: no clauses' typing" fun _ ↦ none
        let c' (Γ : List Tree) : Term := sh (Γ.length - Γ₂.length) c
        (pres "the clauses' type" c' fun pU Γ Φ ψ ↦ do
          let hC := Φ.length - 1
          -- the clauses' type present, as a hypothesis
          let φP := truth P.o (pc P "Prelude.isSome" [c' Γ])
          let dP ← K.solve 3 Γ Φ φP
          let hP := Φ.length
          -- the clauses' type the result type's, by the equality's soundness
          dCut φP dP (decideIn K (fun Γ ↦ apps equalT [atPos pU Γ, atPos pR Γ])
            (refute "the clauses' type another") <|
          K.cutThm "equalSound" (fun Γ ↦ [atPos pU Γ]) <| K.allEΓ (atPos pR) <|
          K.impE (linkK K "cataCore: the clauses' type equal" (K.solve 3)) <| normLastK K <|
          k pB pR hMk rs hC hP) Γ Φ ψ) Γ₂ Φ₂ ψ₂))
        Γ₁ Φ₁ ψ₁) Γ₀ Φ₀ ψ₀
    let srcTest (Γ : List Tree) (t : Term) : Term :=
      pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [sh 1 (numsv Γ), v 0]), t]
    let typedOf (msg : String) (t : List Tree → Term) (k : Deducer) : Deducer :=
      decideIn K (fun Γ ↦ srcTest Γ (t Γ))
        (linkK K s!"cataCore: {msg} no source form" fun Γ Φ ψ ↦
          (K.hypFalse (W.hyp 4) Γ Φ ψ).orElse fun _ ↦
          let e := Φ.length - 1
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ e ++ W.ks.map .delta) .full) e
            (fun Γ Φ ψ ↦ K.hypFalse (W.hyp 4) Γ Φ ψ) Γ Φ ψ) <|
      K.cutThm "typedFixed" (fun Γ ↦ [t Γ]) <| K.allEΓ Ev <| K.allEΓ numsv <|
        K.impE (linkK K s!"cataCore: {msg} a source form" (K.solve 3)) <| normLastK K k
    -- the metadata's erasure's elements the forced map ({name}`eraseMetas`)
    let isListP : Term := Term.lam treeTy (truth P.o (pc P "Datatype.isListTx" [v 0]))
    let metasErased (k : Deducer) : Deducer :=
      K.cutThm "allMono" (fun Γ ↦ [metas Γ]) <| K.allEΓ (fun _ ↦ cataShape P S) <|
      K.allEΓ (fun _ ↦ isListP) <| K.impE (K.byHyp 2) <|
      K.impE (linkK K "cataCore: the metadata's shape" <| dAllI L <| dImpI L <|
        normLastK K <| K.conjE fun Γ Φ ψ ↦
          dConjE L (Φ.length - 2) (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ) Γ Φ ψ) <|
      fun Γ Φ ψ ↦ applyThm K "eraseMetas" (fun Γ ↦ [metas Γ]) [byLast] (fun Γ Φ ψ ↦
          let e := Φ.length - 1
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ e ++ [.delta (T.argIdx 2)]) .full) e k Γ Φ ψ)
          Γ Φ ψ
    let table : List (Term × String) :=
      [(scrutineeName P, "scrutExcluded"), (childrenName P, "childrenExcluded"),
        (atomNameT (pc P "Datatype.aEq" []), "eqExcluded"),
        (atomNameT (pc P "Datatype.aLabel" []), "labelExcluded")]
    let some d := (List.range nQ).foldr (fun _ k ↦ dAllI L k)
        ((List.range W.nH).foldr (fun _ k ↦ dImpI L k) <|
          W.unfold (typedOf "the datatype" dt <| typedOf "the result type" rF <|
            typedOf "the scrutinee" sF <| typedOf "the default" drF <|
            typedOf "the metadata" (fun Γ ↦ pc P "Typing.tList" [metas Γ]) <|
            typing fun pB pR hMk rs hC hP ↦ metasErased <|
            let tools₀ := clauseTools W "Typing.synCata" dt metas metas dt 0 hC hP (bare := true)
            let unitN := atomNameT (pc P "Datatype.aUnitV" [])
            let scope (Γ : List Tree) : Term := scopeOf P (numsv Γ) (cxv Γ)
            let en (t : Term) (Γ : List Tree) : Term := pc P "Reader.expandNums" [numsv Γ, t]
            -- the erasure's parts: the chain, as the resolution's hypothesis reads it
            fun Γ₀ Φ₀ ψ₀ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ₀ (W.hyp 7) ++
              [.delta (P.idx "Datatype.eraseCata")]) .full) (W.hyp 7) (fun Γ₁ Φ₁ ψ₁ ↦
            let hR := Φ₁.length - 1
            (plainAtoms K T (walkAtoms P ++ [childrenName P, nodeName P, resultsName P,
                  unitName P] ++ testPrims P ++ ["aPara", "aUnit", "aUnitV", "aArrow"].map
                    fun a ↦ atomNameT (pc P s!"Datatype.{a}" []))
                numsv (W.hyp 9) (lemmas := table ++ clauseExcluded P ++ cataExcluded P ++
                  [(atomNameT (pc P "Datatype.aPara" []), "paraExcluded")]) <|
              fun Γ₂ Φ₂ ψ₂ ↦ do
              let (t, _) ← evalRw K.G K.E (K.rules Φ₂) .full Γ₂ Φ₂ (← Φ₂[hR]?)
              let some ch := (appsOf K.G (P.idx "Datatype.eraseChain") t).find? fun a ↦
                  (Internal.typeIn K.G 0 Γ₂ a).isSome
                | dbgTrace "cataCore: no chain" fun _ ↦ none
              let w (u : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₂.length) u
              let (s', r') := (er sF, er rF)
              let σ (Γ : List Tree) : List Term := [en (w ch Γ) Γ, en (s' Γ) Γ, en (r' Γ) Γ,
                scope Γ, tysv Γ, namesv Γ]
              let unitAbsent (msg : String) (xs : List Tree → Term) (prf : Deducer) : Deducer :=
                linkK K s!"cataCore: the unit value {msg}" <|
                K.cutThm "indexNone" (fun Γ ↦ [xs Γ]) <| K.allEΓ (fun _ ↦ unitN) <|
                K.impE prf fun Γ Φ ψ ↦ normHyps K [Φ.length - 1] (K.solve 3) Γ Φ ψ
              (applyThm K "cataNums" (fun Γ ↦ [w ch Γ, s' Γ, r' Γ, numsv Γ])
                  ((cataErasureAtoms P).map fun _ ↦ negated) <| normLastK K <|
                (fun k Γ Φ ψ ↦ normHyps K [hR] k Γ Φ ψ) <| fun Γ Φ ψ ↦
                let iRes := Φ.length - 1
                applyThm K "cataParts" σ [K.solve 3, linkK K "cataCore: resolved" (K.byHyp iRes)]
                  (K.conjE <| K.conjE fun Γ Φ ψ ↦
                    let (iRt, iCh, iS) := (Φ.length - 3 - 1, Φ.length - 2, Φ.length - 1)
                    (linkK K "cataCore: the parts" <|
                    applyThm K "cataResEq" σ
                      [K.solve 3, unitAbsent "unscoped" scope (tools₀.unscoped unitN cxv),
                        unitAbsent "undefined" namesv (tools₀.undefined unitN), K.byHyp iRt,
                        K.byHyp iCh, K.byHyp iS] <| normLastK K <|
                    -- the kernel's typing of the resolved term at its parts
                    fun Γ Φ ψ ↦
                    dRwHyp (evalRw K.G K.E (K.rulesEx Φ (W.hyp 8) ++
                      [.delta (P.idx "Datatype.eraseCata")]) .full) (W.hyp 8) (fun Γ Φ ψ ↦
                      let hK := Φ.length - 1
                      applyThm K "cataTyped" (fun Γ ↦ σ Γ ++ [kcv Γ, Gv Γ])
                        [linkK K "cataCore: the resolved term typed" (K.byHyp hK)]
                        (K.conjE fun Γ Φ ψ ↦
                          let (iTc, iTs) := (Φ.length - 2, Φ.length - 1)
                          -- the scrutinee's soundness, its value related at its type
                          (W.soundAtWith (fun i ↦ if i = 7 then some (K.byHyp iS)
                              else if i = 8 then some (K.byHyp iTs) else none) 0
                            (fun _ ↦ none) (fun _ _ _ ↦ none) (fun _ _ _ ↦ none) <|
                            K.convE fun Γ₃ Φ₃ ψ₃ ↦
                            let nS (Δ : List Tree) : Term := v (Δ.length - Γ₃.length + 1)
                            let xS (Δ : List Tree) : Term := v (Δ.length - Γ₃.length)
                            let (sS, rS) := (Φ₃.length - 2, Φ₃.length - 1)
                            (applyThm K "relTDataMember" (fun Δ ↦ [xS Δ, dt Δ, atPos pB Δ, Ev Δ,
                                Dv Δ])
                              [W.byStmt 10, linkK K "cataCore: the datatype named" (K.solve 3),
                                K.byHyp rS] <|
                            K.exE <| K.conjE fun Γ Φ ψ ↦
                            let pt := Γ.length - 1
                            let iMem := Φ.length - 1
                            (fun Γ₄ Φ₄ ψ₄ ↦ do
                              let t₀ ← cataTerms E ix
                              let [A₀] ← nodeKidsT t₀.c | none
                              let tr := atPos pt
                              let Rty := atPos pR
                              let tm (Δ : List Tree) : CataTerms := t₀.inst (σ Δ)
                              let Ar (Δ : List Tree) : Term := Internal.instTerm [] (σ Δ) A₀
                              let kcU (Δ : List Tree) : Term := consT treeTy (tm Δ).tU
                                (consT treeTy (tm Δ).tK (consT treeTy (tm Δ).tO (kcv Δ)))
                              let specs (Δ : List Tree) : Term := Term.snd
                                (pc P "Typing.markerCtors" [ms Δ, dt Δ])
                              let bodies (Δ : List Tree) : Term :=
                                (forcedMapOf K Δ (bodiesF Δ)).getD Term.star
                              let srs (Δ : List Tree) : Term :=
                                pc P "Typing/SRs.drop" [leafT (numeral 5), rs Δ]
                              let rebSR : List Internal.NormRule :=
                                [.thm (ix "rebT") [srTy], .thm (ix "rebL") [srTy, list srTy]]
                              let KL : Kit := { K with more := K.more ++
                                (lookupEqNames.filter fun nm ↦ 0 < ix nm) }
                              let solved : Deducer := fun Γ Φ ψ ↦
                                (K.solve 3 Γ Φ ψ).orElse fun _ ↦ KL.solve 3 Γ Φ ψ
                              let indexT (Δ : List Tree) : Term :=
                                pc P "Prelude.isSome" [markerIdx P (dt Δ) (ms Δ)]
                              -- a hypothesis, both sides with the reader's numeral unfolded, as
                              -- the walk's bindings have it
                              let byNum (i : ℕ) : Deducer := fun Γ Φ ψ ↦
                                let δ : List Internal.NormRule :=
                                  [.delta (P.idx "Reader.numeral")]
                                dRwHyp (evalRw K.G K.E (K.rulesEx Φ i ++ δ) .full) i
                                  (dRwBy (evalRw K.G K.E (K.rules Φ ++ δ) .full) dHyp) Γ Φ ψ
                              -- a membership's test as the datatype's, its marker's index present
                              let fieldAsMember (i : ℕ) : Deducer :=
                                decideIn K indexT
                                  (linkK K "cataCore: no marker's index" fun Γ Φ ψ ↦
                                    (K.hypFalse hMk Γ Φ ψ).orElse fun _ ↦ eqClash K hMk Γ Φ ψ)
                                  (fun Γ Φ ψ ↦ (K.byHyp i Γ Φ ψ).orElse fun _ ↦
                                    let δ : List Internal.NormRule :=
                                      [.delta (P.idx "Typing.fieldOk")]
                                    (dRwHyp (evalRw K.G K.E (K.rulesEx Φ i ++ δ) .full) i
                                      (dRwBy (evalRw K.G K.E (K.rules Φ ++ δ) .full) dHyp) Γ Φ ψ))
                              let cxOk (Rv : List Tree → Term) : Deducer :=
                                let impl : Deducer := solved
                                let consAt (ty : List Tree → Term) (n : Term)
                                    (cxT : List Tree → Term) (prev : Deducer) : Deducer :=
                                  fun Γ Φ ψ ↦
                                  let cons : Deducer := applyThm K "cxTCons"
                                    (fun Δ ↦ [ty Δ, n, Ev Δ, cxT Δ]) [impl, prev] byLast
                                  decideIn K (fun Δ ↦ pc P "Typing.nameOk" [Ev Δ, n]) cons cons
                                    Γ Φ ψ
                                let nm (kw : String) : Term :=
                                  pc P "Typing.boundName" [pc P kw []]
                                consAt (fun _ ↦ pc P "Typing.tyUnit" []) (nm "Typing.kwUnitArg")
                                  (fun Δ ↦ consT treeTy (resultsEntry P (Rv Δ))
                                    (consT treeTy (nodeEntry P) (cxv Δ)))
                                  (consAt (fun Δ ↦ pc P "Typing.tyList" [thunkTy P (Rv Δ)])
                                    (nm "Typing.kwResults")
                                    (fun Δ ↦ consT treeTy (nodeEntry P) (cxv Δ))
                                    (consAt (fun _ ↦ pc P "Typing.tyT" []) (nm "Typing.kwNode") cxv
                                      (W.byStmt cxHyp)))
                              -- the chain's fact, by the chain at the tree and the results
                              let fact : Deducer := dAllI L <| dAllI L <| dAllI L <| dImpI L <|
                                dImpI L <| dImpI L fun Γf Φf ψf ↦
                                let (t', rs', u') := (atPos (Γf.length - 3),
                                  atPos (Γf.length - 2), atPos (Γf.length - 1))
                                let (iLen, iRel, iFok) := (Φf.length - 3, Φf.length - 2,
                                  Φf.length - 1)
                                (applyThm K "memberCtors" (fun Δ ↦ [t' Δ, dt Δ, ms Δ])
                                  [linkK K "cataCore: the child's member" (fieldAsMember iFok)]
                                  fun Γ Φ ψ ↦
                                  let iMember := Φ.length - 1
                                  let tools := clauseTools W "Typing.synCata" specs metas srs t'
                                    iMember hC hP (bare := true)
                                  let kvT (Δ : List Tree) : Term := resultsVal P (Ar Δ) (rs' Δ)
                                  let qT (Δ : List Tree) : Term := pc P "Eval.valQuote" [t' Δ]
                                  let implB (msg : String) : Deducer :=
                                    linkK K s!"cataCore: {msg} bound" solved
                                  let envOk : Deducer :=
                                    applyThm K "envTConsImpl" (fun Δ ↦ [u' Δ, unitEntry P,
                                        consT treeTy (kvT Δ) (consT treeTy (qT Δ) (envv Δ)),
                                        consT treeTy (resultsEntry P (Rty Δ))
                                          (consT treeTy (nodeEntry P) (cxv Δ)), Dv Δ])
                                      [applyThm K "envTConsImpl" (fun Δ ↦ [kvT Δ,
                                          resultsEntry P (Rty Δ), consT treeTy (qT Δ) (envv Δ),
                                          consT treeTy (nodeEntry P) (cxv Δ), Dv Δ])
                                        [applyThm K "envTConsImpl" (fun Δ ↦ [qT Δ, nodeEntry P,
                                            envv Δ, cxv Δ, Dv Δ])
                                          [W.byStmt 1, implB "the node's name"] byLast,
                                          implB "the results' name"] byLast,
                                        implB "the unit's name"] byLast
                                  (K.cutThm "lensEqual" (fun Δ ↦ [bodiesF Δ, Ev Δ]) <| K.conjE <|
                                    fun Γ Φ ψ ↦
                                    let (iA, iB) := (Φ.length - 2, Φ.length - 1)
                                    let lens (msg : String) : Deducer :=
                                      linkK K s!"cataCore: {msg}" fun Γ Φ ψ ↦
                                      dRwBy (evalRw K.G K.E (K.rules Φ ++ rebSR) .full)
                                        (fun Γ Φ ψ ↦ (K.byHyp iA Γ Φ ψ).orElse fun _ ↦
                                          K.byHyp iB Γ Φ ψ) Γ Φ ψ
                                    (K.cutThm "cataChain" (fun Δ ↦ [metas Δ, t' Δ, specs Δ, Ev Δ,
                                        Gv Δ, tysv Δ, numsv Δ, namesv Δ, Dv Δ, Rty Δ, dt Δ, r' Δ,
                                        er drF Δ, rs' Δ, Ar Δ, u' Δ]) <|
                                      K.allEΓ bodies <| K.allEΓ srs <|
                                      K.impE (W.byStmt 10) <| K.impE (W.byStmt 9) <|
                                      K.impE (linkK K "cataCore: the metadata's characters" <|
                                        K.cutThm "cataMetasFixed" (fun Δ ↦ [metas Δ, numsv Δ]) <|
                                        K.impE (linkK K "cataCore: the metadata a source form"
                                          (K.solve 3)) <|
                                        K.impE (linkK K "cataCore: the metadata's shape"
                                          (K.byHyp 2)) byLast) <|
                                      K.impE (linkK K "cataCore: the bodies' soundness" <|
                                        K.cutThm "bodiesLink" (fun Δ ↦ [bodiesF Δ, Ev Δ, Gv Δ,
                                          tysv Δ, numsv Δ, namesv Δ, Dv Δ, W.qv 3 Δ]) <|
                                        ([0, 2, 3, 9, 10, 11].foldr
                                          (fun i k ↦ K.impE (W.byStmt i) k) <|
                                        K.impE (linkK K "cataCore: the bodies source forms" <|
                                          applyThm K "andParts" (fun Δ ↦
                                              [srcTest Δ (pc P "Typing.tList" [bodiesF Δ]),
                                                srcTest Δ (pc P "Typing.tList" [metas Δ])])
                                            [fun Γ Φ ψ ↦
                                              dRwHyp (evalRw K.G K.E (K.rulesEx Φ (W.hyp 4) ++
                                                  [.delta (T.argIdx 5)]) .full) (W.hyp 4)
                                                (dRwBy (evalRw K.G K.E (K.rules Φ ++
                                                  [.delta (T.argIdx 5)]) .full) dHyp) Γ Φ ψ] <|
                                          K.conjE byLast) <|
                                        K.impE (K.byHyp 1) fun Γ Φ ψ ↦
                                          dRwBy (evalRw K.G K.E (K.rules Φ ++ rebSR) .full) byLast
                                            Γ Φ ψ)) <|
                                      K.impE (lens "the bodies' typings' number") <|
                                      K.impE (lens "the bodies' number") <|
                                      K.impE (linkK K "cataCore: the member's constructor"
                                        (K.byHyp iMember)) <|
                                      K.impE (W.byStmt 2) <| K.impE (W.byStmt 3) <|
                                      K.impE (linkK K "cataCore: the results' number"
                                        (K.byHyp iLen)) <|
                                      K.impE (linkK K "cataCore: the results" (K.byHyp iRel)) <|
                                      K.allEΓ cxv <| K.allEΓ envv <| K.allEΓ kcU <|
                                      K.impE (linkK K "cataCore: the coverage" tools.coverage) <|
                                      K.impE (linkK K "cataCore: the agreement" tools.agreement) <|
                                      K.impE (linkK K "cataCore: the environment" envOk) <|
                                      K.impE (linkK K "cataCore: the context" (cxOk Rty)) <|
                                      K.impE (linkK K "cataCore: the chain resolved"
                                        (byNum iCh)) <|
                                      K.impE (linkK K "cataCore: the chain typed" (byNum iTc)) <|
                                      K.impE (tools.unscoped (childrenName P) cxv) <|
                                      K.impE (tools.undefined (childrenName P)) <|
                                      ((testPrims P).foldr (fun n k ↦
                                        K.impE (tools.unscoped n (fun Δ ↦
                                          cataScope P (Rty Δ) (cxv Δ))) <|
                                        K.impE (tools.undefined n) k)) <|
                                      linkK K "cataCore: the chain's conclusion" fun Γ Φ ψ ↦
                                        byNum (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
                                  Γ Φ ψ) Γf Φf ψf
                              let sConv : Deducer := linkK K "cataCore: the scrutinee's value"
                                fun Γ Φ ψ ↦ K.conv nS xS
                                  (K.instN sS (fun _ ↦ v 0) K.byNorm) (K.solve 3) Γ Φ ψ
                              (applyThm K "cataConv" (fun Δ ↦ σ Δ ++ [envv Δ, tr Δ, Rty Δ, Dv Δ,
                                  dt Δ, Ev Δ])
                                [K.solve 3, linkK K "cataCore: the chain's fact" fact, sConv,
                                  linkK K "cataCore: the tree's membership" (fieldAsMember iMem)]
                                (linkK K "cataCore: the conclusion" fun Γc Φc ψc ↦
                                  let iConv := Φc.length - 1
                                  -- the result type the typing's comparison's of itself
                                  (K.cutThm "equalRefl" (fun Δ ↦ [Rty Δ]) fun Γ Φ ψ ↦
                                    let h := Φ.length - 1
                                    decideIn K (fun Δ ↦ apps equalT [Rty Δ, Rty Δ]) (K.hypFalse h)
                                      (fun Γ Φ ψ ↦
                                        dRwBy (fun Γ Φ t ↦ evalRw K.G K.E (K.rules Φ ++
                                          [.delta (P.idx "Typing.synCata"),
                                          .delta (P.idx "Datatype.eraseCata")]) .full Γ Φ t)
                                          (K.byHyp iConv) Γ Φ ψ) Γ Φ ψ) Γc Φc ψc)) Γ₄ Φ₄ ψ₄)
                            Γ Φ ψ) Γ₃ Φ₃ ψ₃) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
                    Γ Φ ψ)
                  Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁) Γ₀ Φ₀ ψ₀) 1)
        a.ctx a.hyps a.concl
      | dbgTrace "cataCore: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness at an expanded structural recursion. -/
def cataCoreDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [appTyped P S, lamTyped P S, cataTyped P S, cataStepOk P S T, cataConv P S T, entriesFixed P S T,
    cataMetasFixed P S T, atomExcluded P S "paraExcluded" (atomNameT (pc P "Datatype.aPara" [])),
    cataCore P S T]

/-- The soundness at an expanded structural recursion, after the fold's. -/
def cataCoreCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := caseNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (caseDev P S T).map (·.1) ++ (clausesDev P S T).map (·.1) ++
    (caseSoundDev P S T).map (·.1) ++ (cataDev P S T).map (·.1) ++
    (cataClausesDev P S T).map (·.1) ++ (cataChainDev P S T).map (·.1) ++
    (cataSoundDev P S T).map (·.1)) "datatype-cata-core" (cataCoreDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
