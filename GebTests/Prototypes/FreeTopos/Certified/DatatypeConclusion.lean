/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeRelation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The conclusion of the datatype language's soundness, in Lean

The soundness of a whole program of the datatype language's stage-1 compiler concludes two
formulas of the internal language, each a definition of the extended program
({lit}`DatatypeAccepted.globDefn`, {lit}`DatatypeAccepted.recsDefn`): that the program's
definitions are related to the typing environment's, and that its datatypes' recognizers
decide membership. Read with the values of the globals the kernel loads, they are statements
of Lean about the evaluator the kernel loads: each name the environment gives a type has an
index among the reader's names, at which the definitions have a term whose evaluation in the
empty environment converges to a value related at the type ({lit}`GlobRel`); and at each
datatype of the environment whose recognizer's name has an index, the definition there
evaluates to a function whose application to the quotation of a tree converges to the
quotation of a tree true exactly when the tree is a member of the datatype ({lit}`RecsRel`).

## Main definitions

* {lit}`GlobRel` — the definitions are related to the typing environment's.
* {lit}`RecsRel` — the recognizers decide membership.
* {lit}`Concl` — the conclusion at a program's forms, as the loaded compilers and evaluator
  compute it.

## Main statements

* {lit}`represents_glob`, {lit}`represents_recs` — the two formulas' arrows represent them.
* {lit}`concl_rep` — the soundness's conclusion at a program's forms represents {lit}`Concl`.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, evaluator, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeConclusion

open Geb Geb.FreeTopos Geb.FreeTopos.Translation GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs pc)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted (statementDefs fnsK envTy envT
  globDefn recsDefn)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated
open GebTests.Prototypes.FreeTopos.Certified.DatatypePasses (Env PassFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeStatements
open GebTests.Prototypes.FreeTopos.Certified.DatatypeRelation
open Internal (Term RepC repC_lam repC_app repC_pair repC_fst repC_snd repC_eq repC_nil
  repC_lnode repC_star objVal_nat objVal_exp objVal_list isTy_nat isTy_list)
open Tactics (apps)
open Kernel (tT tList tProd tArrow)
open Sorts

/-- The program's definitions are related to the typing environment's definitions by the
reader's names, in a context: each name the environment gives a type has an index among the
names, at which the definitions have a term whose evaluation in the empty environment
converges to a value related at the type. -/
def GlobRel (f : EvalFns) (R : Ctx) (E : Env) (names : List Kernel.Tree) : Prop :=
  ∀ n, (f.isSome (f.lookupName n (f.envDefs E))).label ≠ 0 →
    ∃ i, f.indexOf n names = f.just i ∧ ∃ d, f.nth R.1 i = f.just d ∧
      Conv f.just (fun k ↦ (Level f R.1 k).1 [] d)
        (DRel f (f.get (f.lookupName n (f.envDefs E))) R)

/-- The recognizers of the typing environment's datatypes decide membership, in a context: at
each datatype whose recognizer's name has an index among the reader's names, the definitions
have a term there whose evaluation converges to a function, and the function's application to
the quotation of each tree converges to the quotation of a tree true exactly when the tree is
a member of the datatype, by the context's markers. -/
def RecsRel (f : EvalFns) (R : Ctx) (E : Env) (names : List Kernel.Tree) : Prop :=
  ∀ d, (f.hasName d (f.envNoms E)).label ≠ 0 →
    (f.isSome (f.indexOf (f.recognizerName d) names)).label ≠ 0 →
      ∃ i, f.indexOf (f.recognizerName d) names = f.just i ∧ ∃ k, f.nth R.1 i = f.just k ∧
        Conv f.just (fun fuel ↦ (Level f R.1 fuel).1 [] k) fun g ↦ ∀ t,
          Conv f.just (fun fuel ↦ (Level f R.1 fuel).2 g (f.valQuote t)) fun w ↦
            ∃ u, w = f.valQuote u ∧
              ((u.label ≠ 0 → (f.memberOf R.2 (RoseTree.node 1 d.children) t).label ≠ 0) ∧
                ((f.memberOf R.2 (RoseTree.node 1 d.children) t).label ≠ 0 → u.label ≠ 0))

/-- The names the reader reads, as the loaded compilers compute them from a program's
forms. -/
def names (f : PassFns) (ks : List Kernel.Tree) : List Kernel.Tree :=
  (Kernel.Const.child (f.get (f.read ks)) (Kernel.leaf 1)).children

/-- The conclusion of the soundness of a program at its forms, as the loaded compilers and the
loaded evaluator compute it: with the terms the reader reads and the markers of the typing
environment the typing ends in as the relation's context, the definitions are related to the
environment's by the reader's names, and the recognizers decide membership. -/
def Concl (f : PassFns) (g : EvalFns) (ks : List Kernel.Tree) : Prop :=
  GlobRel g (f.terms ks, g.envMs (f.run ks).1) (f.run ks).1 (names f ks) ∧
    RecsRel g (f.terms ks, g.envMs (f.run ks).1) (f.run ks).1 (names f ks)

/-- The conclusion of the soundness of a program at its forms, the variable of the context, as
a formula: the one the soundness's statement has, by the translation of the kernel's child
primitive. -/
def conclT (P : Prog) (T : Defs3) (childT : Term) : Term :=
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let kids (t : Term) : Term := call D.children [] [t]
  let ch (t : Term) (i : ℕ) : Term := apps childT [t, leafT (numeral i)]
  let x := pc P "Datatype.expandTyped" [v 0]
  let ts := Term.snd x
  let nothing := pc P "(Option.nothing Typing.Name)" []
  let run := pc P "Typing.checkAll" [Term.pair (pc P "Typing.env0" []) nothing,
    pc P "Datatype.markersFirst" [ts]]
  let Ev := Term.fst run
  let r := pc P "Recognize.insertRecognizers" [pc P "Datatype.kernelForms" [ts]]
  let b := pc P "Reader.readProgram" [kids (get r)]
  let terms := kids (ch (get b) 0)
  let names := kids (ch (get b) 1)
  let R := Term.pair terms (pc P "Typing.envMs" [Ev])
  Internal.Logic.conj P.o (T.globT R Ev names) (T.recsT R Ev names)

/-- The type of the typing's environments is a type, over every constants. -/
theorem isTy_env (G : Internal.Globals) : Internal.IsTy G 0 envT = true :=
  (ty_spec (G := G) (n := 0) (ρ := []) (ds := []) envTy rfl).1

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST) (L : Translated PST)

include h

/-- The relation at a type in a context, in a context of variables, represents the relation of
Lean ({name}`DRel`) at the type and the context its parts represent. -/
theorem repC_rel {f : EvalFns} (hf : f.Loaded L.Gk PST.1.idx) {X : PartialHorn.Tree}
    {e : List (PartialHorn.Tree × PartialHorn.Tree)} {S A : Type} {R : S → A → Prop}
    {r a : Term} {Rf : S → Ctx} {Af : S → Kernel.Tree}
    (hr : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] r X e Defs3.ctxTy R RCtx Rf)
    (ha : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] a X e treeTy R RT Af) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (PST.2.2.relT r a) X e (exp treeTy omega) R RPred
      fun s ↦ DRel f (Af s) (Rf s) := by
  have hd : PST.1.G.defs[PST.2.2.q]? = some (.language (relDefn PST.1 PST.2.1)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 4) rfl)
  obtain ⟨fc, hdc⟩ := Internal.compiled_language L.ctx.compiles hd
  exact Internal.repC_call₂ (θ := []) (τ' := []) (d := relDefn PST.1 PST.2.1) L.ctx.base hd
    L.ctx.wf hdc rfl rfl (fun _ hu ↦ nomatch hu) .nil rfl rfl (represents_rel h L hf hdc) hr ha

/-- The arrow of the relation of the definitions to the typing environment's represents the
statement of Lean ({name}`GlobRel`), at a context, an environment and names. -/
theorem represents_glob {f : EvalFns} (hf : f.Loaded L.Gk PST.1.idx) {fk : PartialHorn.Tree}
    (hdk : (L.cds₀ ++ L.ext)[PST.2.2.q + 2]? = some ⟨List.replicate 0 obj, arr, fk⟩) :
    Represents [] (unfoldTerm sig (L.cds₀ ++ L.ext) fk)
      (Rep.prod (Rep.prod RCtx (KRel envTy)) (Rep.list RT)) Rep.prop
      fun p : (Ctx × Env) × List Kernel.Tree ↦ GlobRel f p.1.1 p.1.2 p.2 := by
  have hk : PST.1.G.defs[PST.2.2.q + 2]? =
      some (.language (globDefn PST.1 PST.2.1 PST.2.2)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 5) rfl)
  have hEq := DatatypeAccepted.envTy_eq h
  obtain ⟨P, S, T⟩ := PST
  obtain ⟨q, et⟩ := T
  obtain rfl : et = envT := hEq
  have hC := connectives h L
  have hlog := DatatypeAccepted.hasLogic h
  have hT := objVal_tree (ds := L.cds₀ ++ L.ext)
  have hR := objVal_ctx (ds := L.cds₀ ++ L.ext)
  have hL := objVal_list hT
  have hN := objVal_nat (ds := L.cds₀ ++ L.ext) (ρ := [])
  have hTT := objVal_exp hT hT
  have hEnv : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext) envT) (MTy envTy) :=
    objVal_ty' (T := envTy) rfl
  have hops := (ty_spec (G := P.G) (n := 0) (ρ := []) (ds := L.cds₀ ++ L.ext) tT rfl).2.1
  have hvT : ObjVal [] treeTy BT := objVal_ty (T := tT) rfl
  obtain ⟨htot, hsur, hl, hr⟩ := (order_props tT).1 rfl
  have hkNil : P.G.prims[0]? = some Internal.nilPrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  -- the contexts: the parameters, then the name, its index, the definition there, the fuel
  have c₀ := ((RepCtx.single L.ctx hR (isTy_ctx _) RCtx).extend L.ctx hEnv (isTy_env _)
    (KRel envTy)).extend L.ctx hL (by simp [isTy_list, isTy_tree]) (Rep.list RT)
  have c₁ := c₀.extend L.ctx hT (isTy_tree _) RT
  have c₂ := c₁.extend L.ctx hT (isTy_tree _) RT
  have c₃ := c₂.extend L.ctx hT (isTy_tree _) RT
  have c₄ := c₃.extend L.ctx hN isTy_nat Rep.nat
  have hbody := hC.all htot hsur (isTy_tree _) hops hvT
    (repC_lam (G := P.G) (n := 0) (isTy_tree _) c₀.val hT
      (hC.imp
        (repC_truth L.ctx hlog c₁.val (repC_pc₁ L hf.isSome rfl rfl c₁.val
          (repC_pc₂ L hf.lookupName rfl rfl rfl c₁.val (c₁.var (i := 0) rfl)
            (repC_pc₁ L hf.envDefs rfl rfl c₁.val (c₁.var (i := 2) rfl)))))
        (hC.ex htot hsur (isTy_tree _) hops hvT
          (repC_lam (G := P.G) (n := 0) (isTy_tree _) c₁.val hT
            (hC.conj
              (repC_eq
                (repC_pc₂ L hf.indexOf rfl rfl rfl c₂.val (c₂.var (i := 1) rfl)
                  (c₂.var (i := 2) rfl))
                (repC_pc₁ L hf.just rfl rfl c₂.val (c₂.var (i := 0) rfl)) hT hl hr)
              (hC.ex htot hsur (isTy_tree _) hops hvT
                (repC_lam (G := P.G) (n := 0) (isTy_tree _) c₂.val hT
                  (hC.conj
                    (repC_eq
                      (repC_pc₂ L hf.nth rfl rfl rfl c₃.val
                        (repC_fst (c₃.var (i := 5) rfl) hL hL) (c₃.var (i := 1) rfl))
                      (repC_pc₁ L hf.just rfl rfl c₃.val (c₃.var (i := 0) rfl)) hT hl hr)
                    (repC_conv h L hf
                      (repC_lam (G := P.G) (n := 0) isTy_nat c₃.val hN
                        (repC_app (repC_app
                          (repC_fst (repC_level h L hf (repC_fst (c₄.var (i := 6) rfl) hL hL)
                            (c₄.var (i := 0) rfl)) (objVal_exp hL hTT) (objVal_exp hT hTT))
                          (repC_nil hkNil (isTy_tree _) (repC_star c₄.val _) hT RT) hL hTT)
                          (c₄.var (i := 1) rfl) hT hT))
                      (repC_rel h L hf (c₃.var (i := 5) rfl)
                        (repC_pc₁ L hf.get rfl rfl c₃.val
                          (repC_pc₂ L hf.lookupName rfl rfl rfl c₃.val (c₃.var (i := 2) rfl)
                            (repC_pc₁ L hf.envDefs rfl rfl c₃.val
                              (c₃.var (i := 4) rfl))))))))))))))
  exact Internal.rep_def_full (τ' := []) L.ctx.compiles hk hbody (fun _ ↦ rfl) hdk

/-- The arrow of the recognizers' agreement with membership represents the statement of Lean
({name}`RecsRel`), at a context, an environment and names. -/
theorem represents_recs {f : EvalFns} (hf : f.Loaded L.Gk PST.1.idx) {fk : PartialHorn.Tree}
    (hdk : (L.cds₀ ++ L.ext)[PST.2.2.q + 6 + 2 * nFolds]? =
      some ⟨List.replicate 0 obj, arr, fk⟩) :
    Represents [] (unfoldTerm sig (L.cds₀ ++ L.ext) fk)
      (Rep.prod (Rep.prod RCtx (KRel envTy)) (Rep.list RT)) Rep.prop
      fun p : (Ctx × Env) × List Kernel.Tree ↦ RecsRel f p.1.1 p.1.2 p.2 := by
  have hk : PST.1.G.defs[PST.2.2.q + 6 + 2 * nFolds]? =
      some (.language (recsDefn PST.1 PST.2.1 PST.2.2)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 6) rfl)
  have hEq := DatatypeAccepted.envTy_eq h
  obtain ⟨P, S, T⟩ := PST
  obtain ⟨q, et⟩ := T
  obtain rfl : et = envT := hEq
  have hC := connectives h L
  have hlog := DatatypeAccepted.hasLogic h
  have hT := objVal_tree (ds := L.cds₀ ++ L.ext)
  have hB := objVal_bits (ds := L.cds₀ ++ L.ext)
  have hR := objVal_ctx (ds := L.cds₀ ++ L.ext)
  have hL := objVal_list hT
  have hN := objVal_nat (ds := L.cds₀ ++ L.ext) (ρ := [])
  have hTT := objVal_exp hT hT
  have hEnv : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext) envT) (MTy envTy) :=
    objVal_ty' (T := envTy) rfl
  have hops := (ty_spec (G := P.G) (n := 0) (ρ := []) (ds := L.cds₀ ++ L.ext) tT rfl).2.1
  have hvT : ObjVal [] treeTy BT := objVal_ty (T := tT) rfl
  obtain ⟨htot, hsur, hl, hr⟩ := (order_props tT).1 rfl
  have hkNil : P.G.prims[0]? = some Internal.nilPrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  have hkNode : P.G.prims[2]? = some Internal.lnodePrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  -- the contexts: the parameters, then the datatype, the index, the definition there; the fuel
  -- of its evaluation; its value, a tree; the fuel of the application; its value, and a tree
  have c₀ := ((RepCtx.single L.ctx hR (isTy_ctx _) RCtx).extend L.ctx hEnv (isTy_env _)
    (KRel envTy)).extend L.ctx hL (by simp [isTy_list, isTy_tree]) (Rep.list RT)
  have c₁ := c₀.extend L.ctx hT (isTy_tree _) RT
  have c₂ := c₁.extend L.ctx hT (isTy_tree _) RT
  have c₃ := c₂.extend L.ctx hT (isTy_tree _) RT
  have c₄n := c₃.extend L.ctx hN isTy_nat Rep.nat
  have c₄ := c₃.extend L.ctx hT (isTy_tree _) RT
  have c₅ := c₄.extend L.ctx hT (isTy_tree _) RT
  have c₆n := c₅.extend L.ctx hN isTy_nat Rep.nat
  have c₆ := c₅.extend L.ctx hT (isTy_tree _) RT
  have c₇ := c₆.extend L.ctx hT (isTy_tree _) RT
  -- the tree's membership in the datatype
  have hmem := repC_truth L.ctx hlog c₇.val
    (repC_pc₃ L hf.memberOf rfl rfl rfl rfl c₇.val (repC_snd (c₇.var (i := 9) rfl) hL hL)
      (repC_lnode hkNode (isTy_bits _)
        (repC_pair (c₇.numeral L.ctx 1) (repC_children L.ctx (c₇.var (i := 6) rfl))) hB)
      (c₇.var (i := 2) rfl))
  have htrue := repC_truth L.ctx hlog c₇.val (c₇.var (i := 0) rfl)
  -- the application's value quotes a tree true exactly at a member
  have hagrees := hC.ex htot hsur (isTy_tree _) hops hvT
    (repC_lam (G := P.G) (n := 0) (isTy_tree _) c₆.val hT
      (hC.conj
        (repC_eq (c₇.var (i := 1) rfl)
          (repC_pc₁ L hf.valQuote rfl rfl c₇.val (c₇.var (i := 0) rfl)) hT hl hr)
        (hC.conj (hC.imp htrue hmem) (hC.imp hmem htrue))))
  -- the function's application to a tree's quotation converges to such a value
  have happlied := repC_conv h L hf
    (repC_lam (G := P.G) (n := 0) isTy_nat c₅.val hN
      (repC_app (repC_app
        (repC_snd (repC_level h L hf (repC_fst (c₆n.var (i := 8) rfl) hL hL)
          (c₆n.var (i := 0) rfl)) (objVal_exp hL hTT) (objVal_exp hT hTT))
        (c₆n.var (i := 2) rfl) hT hTT)
        (repC_pc₁ L hf.valQuote rfl rfl c₆n.val (c₆n.var (i := 1) rfl)) hT hT))
    (repC_lam (G := P.G) (n := 0) (isTy_tree _) c₅.val hT hagrees)
  -- the definition at the index evaluates to such a function
  have hrecog := hC.conj
    (repC_eq
      (repC_pc₂ L hf.nth rfl rfl rfl c₃.val (repC_fst (c₃.var (i := 5) rfl) hL hL)
        (c₃.var (i := 1) rfl))
      (repC_pc₁ L hf.just rfl rfl c₃.val (c₃.var (i := 0) rfl)) hT hl hr)
    (repC_conv h L hf
      (repC_lam (G := P.G) (n := 0) isTy_nat c₃.val hN
        (repC_app (repC_app
          (repC_fst (repC_level h L hf (repC_fst (c₄n.var (i := 6) rfl) hL hL)
            (c₄n.var (i := 0) rfl)) (objVal_exp hL hTT) (objVal_exp hT hTT))
          (repC_nil hkNil (isTy_tree _) (repC_star c₄n.val _) hT RT) hL hTT)
          (c₄n.var (i := 1) rfl) hT hT))
      (repC_lam (G := P.G) (n := 0) (isTy_tree _) c₃.val hT
        (hC.all htot hsur (isTy_tree _) hops hvT
          (repC_lam (G := P.G) (n := 0) (isTy_tree _) c₄.val hT happlied))))
  have hbody := hC.all htot hsur (isTy_tree _) hops hvT
    (repC_lam (G := P.G) (n := 0) (isTy_tree _) c₀.val hT
      (hC.imp
        (repC_truth L.ctx hlog c₁.val
          (repC_pc₂ L hf.hasName rfl rfl rfl c₁.val (c₁.var (i := 0) rfl)
            (repC_pc₁ L hf.envNoms rfl rfl c₁.val (c₁.var (i := 2) rfl))))
        (hC.imp
          (repC_truth L.ctx hlog c₁.val (repC_pc₁ L hf.isSome rfl rfl c₁.val
            (repC_pc₂ L hf.indexOf rfl rfl rfl c₁.val
              (repC_pc₁ L hf.recognizerName rfl rfl c₁.val (c₁.var (i := 0) rfl))
              (c₁.var (i := 1) rfl))))
          (hC.ex htot hsur (isTy_tree _) hops hvT
            (repC_lam (G := P.G) (n := 0) (isTy_tree _) c₁.val hT
              (hC.conj
                (repC_eq
                  (repC_pc₂ L hf.indexOf rfl rfl rfl c₂.val
                    (repC_pc₁ L hf.recognizerName rfl rfl c₂.val (c₂.var (i := 1) rfl))
                    (c₂.var (i := 2) rfl))
                  (repC_pc₁ L hf.just rfl rfl c₂.val (c₂.var (i := 0) rfl)) hT hl hr)
                (hC.ex htot hsur (isTy_tree _) hops hvT
                  (repC_lam (G := P.G) (n := 0) (isTy_tree _) c₂.val hT hrecog))))))))
  exact Internal.rep_def_full (τ' := []) L.ctx.compiles hk hbody (fun _ ↦ rfl) hdk

/-- The relation of the definitions to the typing environment's, in a context of variables,
represents the statement of Lean ({name}`GlobRel`) at what its parts represent. -/
theorem repC_glob {f : EvalFns} (hf : f.Loaded L.Gk PST.1.idx) {X : PartialHorn.Tree}
    {e : List (PartialHorn.Tree × PartialHorn.Tree)} {S A : Type} {R : S → A → Prop}
    {r ev ns : Term} {Rf : S → Ctx} {Ef : S → Env} {Nf : S → List Kernel.Tree}
    (hr : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] r X e Defs3.ctxTy R RCtx Rf)
    (he : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] ev X e envT R (KRel envTy) Ef)
    (hn : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] ns X e (list treeTy) R (Rep.list RT) Nf) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (PST.2.2.globT r ev ns) X e omega R Rep.prop
      fun s ↦ GlobRel f (Rf s) (Ef s) (Nf s) := by
  have hd : PST.1.G.defs[PST.2.2.q + 2]? =
      some (.language (globDefn PST.1 PST.2.1 PST.2.2)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 5) rfl)
  have hEq := DatatypeAccepted.envTy_eq h
  obtain ⟨P, S, T⟩ := PST
  obtain ⟨q, et⟩ := T
  obtain rfl : et = envT := hEq
  obtain ⟨fc, hdc⟩ := Internal.compiled_language L.ctx.compiles hd
  exact Internal.repC_call₃ (θ := []) (τ' := []) (d := globDefn P S ⟨q, envT⟩) L.ctx.base hd
    L.ctx.wf hdc rfl rfl (fun _ hu ↦ nomatch hu) .nil rfl rfl (represents_glob h L hf hdc) hr he
    hn

/-- The recognizers' agreement with membership, in a context of variables, represents the
statement of Lean ({name}`RecsRel`) at what its parts represent. -/
theorem repC_recs {f : EvalFns} (hf : f.Loaded L.Gk PST.1.idx) {X : PartialHorn.Tree}
    {e : List (PartialHorn.Tree × PartialHorn.Tree)} {S A : Type} {R : S → A → Prop}
    {r ev ns : Term} {Rf : S → Ctx} {Ef : S → Env} {Nf : S → List Kernel.Tree}
    (hr : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] r X e Defs3.ctxTy R RCtx Rf)
    (he : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] ev X e envT R (KRel envTy) Ef)
    (hn : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] ns X e (list treeTy) R (Rep.list RT) Nf) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (PST.2.2.recsT r ev ns) X e omega R Rep.prop
      fun s ↦ RecsRel f (Rf s) (Ef s) (Nf s) := by
  have hd : PST.1.G.defs[PST.2.2.q + 6 + 2 * nFolds]? =
      some (.language (recsDefn PST.1 PST.2.1 PST.2.2)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 6) rfl)
  have hEq := DatatypeAccepted.envTy_eq h
  obtain ⟨P, S, T⟩ := PST
  obtain ⟨q, et⟩ := T
  obtain rfl : et = envT := hEq
  obtain ⟨fc, hdc⟩ := Internal.compiled_language L.ctx.compiles hd
  exact Internal.repC_call₃ (θ := []) (τ' := []) (d := recsDefn P S ⟨q, envT⟩) L.ctx.base hd
    L.ctx.wf hdc rfl rfl (fun _ hu ↦ nomatch hu) .nil rfl rfl (represents_recs h L hf hdc) hr he
    hn

/-- The conclusion of the soundness of a program at its forms ({name}`conclT`) represents the
conclusion as the loaded compilers and the loaded evaluator compute it ({name}`Concl`), at the
kernel's lists of trees. -/
theorem concl_rep {f : PassFns} (hf : f.Loaded L.Gk PST.1.idx) {g : EvalFns}
    (hg : g.Loaded L.Gk PST.1.idx) {childT : Term}
    (hch : primT Kernel.Prim.child = some childT) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (conclT PST.1 PST.2.2 childT)
      (Internal.ctxObj [list treeTy]) (Internal.stdEnv [list treeTy]) omega (KRel (tList tT))
      Rep.prop (Concl f g) := by
  have hC := connectives h L
  have hT := objVal_tree (ds := L.cds₀ ++ L.ext)
  have hL := objVal_list hT
  have hTT := objVal_exp hT hT
  have hEnv : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext) envT) (MTy envTy) :=
    objVal_ty' (T := envTy) rfl
  -- the context of the forms
  have c := RepCtx.single L.ctx hL (by simp [isTy_list, isTy_tree]) (Rep.list RT)
  -- the expansion, the typing, the recognizers and the reading
  have hx := repC_pc₁ L hf.expandTyped rfl rfl c.val (c.var (i := 0) rfl)
  have hts := repC_snd hx hT hL
  have hrun := repC_pc₂ L hf.checkAll rfl rfl rfl c.val
    (repC_pair (repC_pc₀ L hf.env0 rfl c.val (Rep.list RT))
      (repC_pc₀ L hf.nothing rfl c.val (Rep.list RT)))
    (repC_pc₁ L hf.markersFirst rfl rfl c.val hts)
  have hEv := repC_fst hrun hEnv hT
  have hb := repC_pc₁ L hf.readProgram rfl rfl c.val
    (repC_children L.ctx (repC_pc₁ L hf.get rfl rfl c.val
      (repC_pc₁ L hf.insertRecognizers rfl rfl c.val
        (repC_pc₁ L hf.kernelForms rfl rfl c.val hts))))
  -- the terms and the names the reader reads: the children of its reading's children
  obtain ⟨a, ha, hchild⟩ := c.prim L.ctx (k := Kernel.Prim.child)
    (g := ⟨tArrow tT (tArrow tT tT), Kernel.Const.child⟩) rfl hch
  obtain rfl : a = exp treeTy (exp treeTy treeTy) := Option.some.inj (ha.symm.trans rfl)
  have hgb := repC_pc₁ L hf.get rfl rfl c.val hb
  have hterms := repC_children L.ctx
    (repC_app (repC_app hchild hgb hT hTT) (c.quote L.ctx (Kernel.leaf 0)) hT hT)
  have hnames := repC_children L.ctx
    (repC_app (repC_app hchild hgb hT hTT) (c.quote L.ctx (Kernel.leaf 1)) hT hT)
  have hR := repC_pair hterms (repC_pc₁ L hg.envMs rfl rfl c.val hEv)
  exact hC.conj (repC_glob h L hg hR hEv hnames) (repC_recs h L hg hR hEv hnames)

end GebTests.Prototypes.FreeTopos.Certified.DatatypeConclusion

end
