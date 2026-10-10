/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Language

set_option doc.verso true in
/-!
# The derivations and developments in the checker written in Geb

The functions of {lit}`bootstrap/free-topos/derivation.geb`, in the Lean the bootstrap compiler
emits ({lit}`GebMirror.Metalogic`), agree with the Lean checker of the internal language's
derivations and developments at every encoded input: the rewriting of a term at its root by each
rule of the language's equations, the steps of the rewriting and of the proving at a node of each
rule, the checker of derivations, and the step of a development at each kind of declaration.

The mirror's rewriting step selects its rule by a chain of tests of the rule's position; its
proving step likewise. Each rule is proved in a lemma of its own, the chain's tests evaluated
before its branches are simplified, so that the other rules' branches are not.

## Main definitions

* {lit}`encCtx` — a context with hypotheses as a tree.
* {lit}`DRel` — the relation of the mirror's rewriting and proving of a derivation to the
  checker's.

## Main statements

* {lit}`rootStep_eq` — the rewriting of a term at its root by a rule.
* {lit}`rewriteStep_eq`, {lit}`proveStep_eq` — the rewriting and the proving at a node of a rule.
* {lit}`check_eq` — the checker of a derivation.
* {lit}`thmChecks_eq` — the test that a derivation proves a theorem.
* {lit}`declStep_eq` — the state after a declaration.
* {lit}`checkDev_eq` — the state after a development.

## Tags

internal language, derivation, development, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Derivation

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Fold GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.PartialHorn GebTests.Prototypes.FreeTopos.Agreement.Theory
  GebTests.Prototypes.FreeTopos.Agreement.Infer GebTests.Prototypes.FreeTopos.Agreement.Language
open Internal (Term Label)
open scoped FinEnum

/-- The mirror's bindings and images of optional values are the base's of optional trees. -/
@[template] theorem bindPT_def : «Derivation.bindPT» = «Base.bindO» := rfl

@[template, inherit_doc bindPT_def] theorem bindHT_def : «Derivation.bindHT» = «Base.bindO» := rfl

@[template, inherit_doc bindPT_def] theorem bindEH_def : «Derivation.bindEH» = «Base.bindO» := rfl

@[template, inherit_doc bindPT_def] theorem bindTS_def : «Derivation.bindTS» = «Base.bindO» := rfl

@[template, inherit_doc bindPT_def] theorem bindST_def : «Derivation.bindST» = «Base.bindO» := rfl

@[template, inherit_doc bindPT_def] theorem bindPD_def : «Derivation.bindPD» = «Base.bindO» := rfl

@[template, inherit_doc bindPT_def] theorem bindRD_def : «Derivation.bindRD» = «Base.bindO» := rfl

@[template, inherit_doc bindPT_def] theorem bindHD_def : «Derivation.bindHD» = «Base.bindO» := rfl

@[template, inherit_doc bindPT_def] theorem bindTD_def : «Derivation.bindTD» = «Base.bindO» := rfl

@[template, inherit_doc bindPT_def] theorem bindSD_def : «Derivation.bindSD» = «Base.bindO» := rfl

@[template, inherit_doc bindPT_def] theorem mapPT_def : «Derivation.mapPT» = «Base.mapO» := rfl

@[template, inherit_doc bindPT_def] theorem mapLT_def : «Derivation.mapLT» = «Base.mapO» := rfl

/-- The mirror's theorem among the entries at a position is the base's binding of the entry. -/
@[template] theorem thmAt_def :
    «Derivation.thmAt» = fun E i ↦ «Base.bindO» («Prelude.nth» E i) «Derivation.entryLanguage» := by
  funext E i
  simp only [«Derivation.thmAt», template]

/-- The mirror's optional hypotheses, each present, are the base's optional trees. -/
@[template] theorem allSomeTerms_def : «Derivation.allSomeTerms» = «Base.allSomeT» := rfl

/-- The mirror's extensions of the primitive arrows and the definitions are its pushing of an
entry. -/
@[template] theorem pushPrim_def : «Derivation.pushPrim» = «Derivation.push» := rfl

@[template, inherit_doc pushPrim_def] theorem pushDef_def :
    «Derivation.pushDef» = «Derivation.push» := rfl

/-- The mirror's scope of a context and hypotheses is their pair. -/
@[template] theorem scope_def : «Derivation.scope» = «Language.pr» := rfl

/-- The mirror's state of a development is the pair of its constants and the node of its entries. -/
@[template] theorem devState_def : «Derivation.devState» = «Language.pr» := rfl

@[template, inherit_doc devState_def] theorem stateOf_def :
    «Derivation.stateOf» = fun G E ↦ «Language.pr» G (RoseTree.node 0 E) := rfl

/-- The mirror's constants and entries of a state are the pair's components. -/
@[template] theorem stConsts_def : «Derivation.stConsts» = «Language.p1» := rfl

@[template, inherit_doc stConsts_def] theorem stEntries_def :
    «Derivation.stEntries» = fun s ↦ Const.children («Language.p2» s) := rfl

/-- The mirror's lists of definitions and of scopes, each the elements of a node. -/
@[simp, template] theorem pdefnsOf_node (xs : List Tree) :
    «Derivation.pdefnsOf» (RoseTree.node 0 xs) = xs := by
  simp [«Derivation.pdefnsOf»]

@[simp, template, inherit_doc pdefnsOf_node] theorem scopesOf_node (xs : List Tree) :
    «Derivation.scopesOf» (RoseTree.node 0 xs) = xs := by
  simp [«Derivation.scopesOf»]

/-- The mirror's present hypotheses. -/
@[simp, template] theorem termsOr_some (xs : List Tree) :
    «Derivation.termsOr» (encOpt (some (RoseTree.node 0 xs))) = xs := by
  simp [«Derivation.termsOr», encOpt]

/-- The mirror's context and hypotheses of a scope. -/
@[simp, template] theorem scopeCtx_pair (a b : List Tree) :
    «Derivation.scopeCtx» (encPair (RoseTree.node 0 a, RoseTree.node 0 b)) = a := by
  simp [«Derivation.scopeCtx», encPair]

@[simp, template, inherit_doc scopeCtx_pair] theorem scopeHyps_pair (a b : List Tree) :
    «Derivation.scopeHyps» (encPair (RoseTree.node 0 a, RoseTree.node 0 b)) = b := by
  simp [«Derivation.scopeHyps», encPair]

/-- The mirror's lists wrapped as datatypes, each the node of label zero over its elements. -/
@[simp, template] theorem terms_wrap (xs : List Tree) :
    «Derivation.terms» xs = RoseTree.node 0 xs := rfl

@[simp, template, inherit_doc terms_wrap] theorem scopes_wrap (xs : List Tree) :
    «Derivation.scopes» xs = RoseTree.node 0 xs := rfl

@[simp, template, inherit_doc terms_wrap] theorem entries_wrap (xs : List Tree) :
    «Derivation.entries» xs = RoseTree.node 0 xs := rfl

/-- The leaf of label zero is a truth value exactly when it is false. -/
theorem leaf_zero_eq_ofBool (b : Bool) : (leaf 0 = ofBool b) = (b = false) := by
  cases b <;> simp [ofBool_false, ofBool_true, leaf_inj]

/-- The simplification of the mirror's derivation checker: the lemmas of {lit}`mirror_simp`,
the accessors and constructors of encoded terms, pairs, and the given lemmas. -/
local macro "der_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  mirror_simp [mIs_eq, mArg_eq, mD_eq, mArgs_eq, mData_eq, label_encTerm, mVar_eq, mStar_eq,
    mPair_eq, mFst_eq, mSnd_eq, mLam_eq, mApp_eq, mArr_eq, mNatRec_eq, mListRec_eq, mRoseRec_eq,
    mDefn_eq, mEq_eq, pr_eq, p1_eq, p2_eq, none_eq, some_eq, beq_iff_eq, Nat.add_one_ne_zero,
    Nat.reduceEqDiff, Option.elim_map, Option.map_bind, Option.bind_eq_bind, Option.pure_def,
    Bool.and_eq_true, decide_eq_true_eq, false_and, and_false, true_and, and_true, List.getD_nil,
    List.isEmpty_cons, List.isEmpty_nil, Bool.or_eq_true, leaf_zero_eq_ofBool, $ls,*] $(loc)?)

/-- The mirror's primitive arrow zero. -/
@[simp] theorem zeroPrim_eq : «Derivation.zeroPrim» = encPrim Internal.zeroPrim := rfl

/-- The mirror's primitive arrow successor. -/
@[simp] theorem succPrim_eq : «Derivation.succPrim» = encPrim Internal.succPrim := rfl

/-- The mirror's primitive arrow of the empty list. -/
@[simp] theorem nilPrim_eq : «Derivation.nilPrim» = encPrim Internal.nilPrim := rfl

/-- The mirror's primitive arrow of the construction of a list. -/
@[simp] theorem consPrim_eq : «Derivation.consPrim» = encPrim Internal.consPrim := rfl

/-- The mirror's primitive arrow of the construction of a rose tree. -/
@[simp] theorem nodePrim_eq : «Derivation.nodePrim» = encPrim Internal.nodePrim := rfl

/-- The mirror's primitive arrow of the construction of a rose tree over labels. -/
@[simp] theorem lnodePrim_eq : «Derivation.lnodePrim» = encPrim Internal.lnodePrim := rfl

/-- The mirror's primitive arrow of the left injection. -/
@[simp] theorem inlPrim_eq : «Derivation.inlPrim» = encPrim Internal.inlPrim := rfl

/-- The mirror's primitive arrow of the right injection. -/
@[simp] theorem inrPrim_eq : «Derivation.inrPrim» = encPrim Internal.inrPrim := rfl

/-- The mirror's primitive arrow of the case analysis of a coproduct. -/
@[simp] theorem casePrim_eq : «Derivation.casePrim» = encPrim Internal.casePrim := rfl

/-- Encoded primitive arrows are equal exactly when the primitive arrows are. -/
theorem encPrim_inj {p q : Internal.Prim} : encPrim p = encPrim q ↔ p = q := by
  refine ⟨fun h ↦ ?_, congrArg encPrim⟩
  obtain ⟨m, f, a, b⟩ := p
  obtain ⟨m', f', a', b'⟩ := q
  simp only [encPrim, node_inj, List.cons.injEq, leaf_inj, and_true, true_and] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- The mirror's test that the primitive arrow of an index is a given one. -/
theorem primIs_eq (G : Internal.Globals) (k : ℕ) (p : Internal.Prim) :
    «Derivation.primIs» (encGlobals G) (leaf k) (encPrim p) =
      ofBool (decide (G.prims[k]? = some p)) := by
  simp only [«Derivation.primIs», template, gPrims_eq, nth_eq, List.getElem?_map, some_eq, equal_eq]
  congr 1
  cases G.prims[k]? <;> simp [encOpt_inj, encPrim_inj]

/-- The mirror's object variables. -/
@[simp] theorem objVars_eq (n : ℕ) :
    «Derivation.objVars» (leaf n) = Internal.objVars n := by
  simp [«Derivation.objVars», Internal.objVars, Function.comp_def]

/-- The mirror's substitution of a term for the innermost variable, the others lowered. -/
theorem instVar_eq (u : Term) (i : ℕ) :
    «Derivation.instVar» (encTerm u) (leaf i) = encTerm (Internal.instVar u i) := by
  cases i <;> mirror_simp [«Derivation.instVar», Internal.instVar, mVar_eq, beq_iff_eq,
    Nat.add_one_ne_zero, Nat.add_sub_cancel]

/-- The mirror's substitution of two terms for the two innermost variables, the others
lowered. -/
theorem instVar2_eq (u v : Term) (i : ℕ) :
    «Derivation.instVar2» (encTerm u) (encTerm v) (leaf i) =
      encTerm (Internal.instVar2 u v i) := by
  rcases i with _ | _ | i <;> mirror_simp [«Derivation.instVar2», Internal.instVar2, mVar_eq,
    beq_iff_eq, Nat.add_one_ne_zero, Nat.add_sub_cancel]
  simp only [eq_false fun h : i + 1 + 1 = 1 ↦ Nat.succ_ne_zero i (Nat.succ.inj h), ↓reduceIte,
    show i + 1 + 1 - 2 = i from Nat.add_sub_cancel i 2]

/-- The mirror's substitution of a term for the innermost variable, the others in place. -/
theorem atVar0_eq (u : Term) (i : ℕ) :
    «Derivation.atVar0» (encTerm u) (leaf i) = encTerm (Internal.atVar0 u i) := by
  cases i <;> mirror_simp [«Derivation.atVar0», Internal.atVar0, mVar_eq, beq_iff_eq,
    Nat.add_one_ne_zero]

/-- The mirror's term at the successor of its natural number variable. -/
@[simp] theorem natSuccAt_eq (ks : ℕ) (t : Term) :
    «Derivation.natSuccAt» (leaf ks) (encTerm t) = encTerm (Internal.natSuccAt ks t) := by
  simp only [«Derivation.natSuccAt», template, Internal.natSuccAt, mVar_eq, mArr_eq]
  exact subst_eq _ _ _ (atVar0_eq _)

/-- The mirror's term at the construction of a list before its list variable. -/
@[simp] theorem listConsAt_eq (kc : ℕ) (a : Tree) (t : Term) :
    «Derivation.listConsAt» (leaf kc) a (encTerm t) =
      encTerm (Internal.listConsAt kc a t) := by
  simp only [«Derivation.listConsAt», template, Internal.listConsAt]
  refine subst_eq _ _ _ fun i ↦ ?_
  cases i <;> mirror_simp [mVar_eq, mPair_eq, mArr_eq, beq_iff_eq, Nat.add_one_ne_zero]

/-- The mirror's term at the construction of a rose tree. -/
@[simp] theorem roseNodeAt_eq (kn : ℕ) (r a : Tree) (t : Term) :
    «Derivation.roseNodeAt» (leaf kn) r a (encTerm t) =
      encTerm (Internal.roseNodeAt kn r a t) := by
  simp only [«Derivation.roseNodeAt», template, Internal.roseNodeAt, mVar_eq, mPair_eq, mArr_eq,
    equal_eq, mirror_rose, label_ne_zero, ofBool_bne, decide_eq_true_eq, single_eq]
  split_ifs <;> exact subst_eq _ _ _ (instVar_eq _)

/-- The mirror's weakening of a term past an element after its list variable. -/
@[simp] theorem weakenElem_eq (t : Term) :
    «Derivation.weakenElem» (encTerm t) = encTerm (Internal.weakenElem t) := by
  refine rename_eq _ _ _ fun i ↦ ?_
  cases i <;> mirror_simp [beq_iff_eq, Nat.add_one_ne_zero]

/-- The mirror's weakening of a term past a new innermost variable. -/
@[simp] theorem weaken1_eq (t : Term) :
    «Derivation.weaken1» (encTerm t) = encTerm (Internal.weaken1 t) :=
  rename_eq _ _ _ fun _ ↦ rfl

/-- The mirror's weakening of a term past two new innermost variables. -/
@[simp] theorem weaken2_eq (t : Term) :
    «Derivation.weaken2» (encTerm t) = encTerm (Internal.weaken2 t) :=
  rename_eq _ _ _ fun _ ↦ rfl

/-- The mirror's weakening of a rose-tree fold's step past two variables below its own. -/
@[simp] theorem weakenStep2_eq (s : Term) :
    «Derivation.weakenStep2» (encTerm s) = encTerm (Internal.weakenStep2 s) := by
  refine rename_eq _ _ _ fun i ↦ ?_
  cases i <;> mirror_simp [beq_iff_eq, Nat.add_one_ne_zero, Internal.Term.liftR, Nat.add_right_comm]

/-- The mirror's lowering of a term's variables by one. -/
@[simp] theorem lower1_eq (t : Term) :
    «Derivation.lower1» (encTerm t) = encTerm (Internal.Term.rename t (· - 1)) :=
  rename_eq _ _ _ fun _ ↦ rfl

/-- The mirror's list of a term's values at a rose tree's children. -/
@[simp] theorem roseMapAt_eq (kl kc : ℕ) (c : Tree) (t : Term) :
    «Derivation.roseMapAt» (leaf kl) (leaf kc) c (encTerm t) =
      encTerm (Internal.roseMapAt kl kc c t) := by
  simp only [«Derivation.roseMapAt», template, Internal.roseMapAt, weaken1_eq, mVar_eq, mPair_eq,
    mStar_eq, single_eq, mArr_eq, mListRec_eq]

/-- The mirror's hypothesis of induction on rose trees. -/
@[simp] theorem roseHyp_eq (kl kc : ℕ) (φ : Term) :
    «Derivation.roseHyp» (leaf kl) (leaf kc) (encTerm φ) =
      encTerm (Internal.roseHyp kl kc φ) := by
  simp only [«Derivation.roseHyp», template, Internal.roseHyp, mStar_eq, mEq_eq, roseMapAt_eq,
    mirror_omega]

/-- The mirror's sides of an equation. -/
theorem eqParts_eq (φ : Term) :
    «Derivation.eqParts» (encTerm φ) =
      encOpt ((Internal.eqParts φ).map fun p ↦ encPair (encTerm p.1, encTerm p.2)) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, φ = RoseTree.node l cs :=
    ⟨φ.label, φ.children, (RoseTree.node_label_children φ).symm⟩
  cases l <;> rcases cs with _ | ⟨t, _ | ⟨u, _ | ⟨w, cs⟩⟩⟩ <;>
    der_simp [«Derivation.eqParts», Internal.eqParts, labelData]

/-- The mirror's instance of a theorem's term at objects and terms. -/
@[simp] theorem instTerm_eq (θ : List Tree) (σ : List Term) (s : Term) :
    «Derivation.instTerm» θ (σ.map encTerm) (encTerm s) =
      encTerm (Internal.instTerm θ σ s) := by
  simp only [«Derivation.instTerm», template, Internal.instTerm, osubst_eq]
  exact subst_eq _ _ _ (substList_eq σ)

/-- The mirror's type of a term in a context. -/
@[simp] theorem typeIn_eq (G : Internal.Globals) (n : ℕ) (Γ : List Tree) (t : Term) :
    «Derivation.typeIn» (encGlobals G) (leaf n) Γ (encTerm t) =
      encOpt (Internal.typeIn G n Γ t) := by
  have hc := compile_eq G n t (Internal.ctxObj Γ) (Internal.stdEnv Γ)
  simp only [«Derivation.typeIn», template, ctxObj_eq, stdEnv_eq, hc, mapO_eq, Option.map_map,
    Internal.typeIn]
  rfl

/-- The mirror's test that a term is a formula in a context. -/
@[simp] theorem isFormula_eq (G : Internal.Globals) (n : ℕ) (Γ : List Tree) (t : Term) :
    «Derivation.isFormula» (encGlobals G) (leaf n) Γ (encTerm t) =
      ofBool (decide (Internal.typeIn G n Γ t = some omega)) := by
  simp [«Derivation.isFormula», some_eq, encOpt_inj]

/-- The mirror's hypotheses lowered past an innermost variable none of them mentions. -/
theorem lowerHyps_eq (G : Internal.Globals) (n : ℕ) (Γ : List Tree) (Φ : List Term) :
    «Derivation.lowerHyps» (encGlobals G) (leaf n) Γ (Φ.map encTerm) =
      encOpt ((Internal.lowerHyps G n Γ Φ).map fun Φ' ↦ RoseTree.node 0 (Φ'.map encTerm)) := by
  have hf : ∀ ψ : Term, (fun h ↦
      let l := «Derivation.lower1» h
      if («Prelude.and» (Const.equal («Derivation.weaken1» l) h)
          («Derivation.isFormula» (encGlobals G) (leaf n) Γ l)).label ≠ 0 then
        «Prelude.some» l else «Prelude.none») (encTerm ψ) =
      encOpt ((if Internal.weaken1 (Internal.Term.rename ψ (· - 1)) = ψ ∧
          Internal.typeIn G n Γ (Internal.Term.rename ψ (· - 1)) = some omega
        then some (Internal.Term.rename ψ (· - 1)) else none).map encTerm) := fun ψ ↦ by
    mirror_simp [lower1_eq, weaken1_eq, isFormula_eq, encTerm_eq_iff, some_eq, none_eq,
      Bool.and_eq_true, decide_eq_true_eq]
    split_ifs <;> rfl
  simp only [«Derivation.lowerHyps», template, mapT_eq, List.map_map, Function.comp_def, hf]
  rw [allSomeT_eq, mapM_map_option, Option.map_map]
  rfl

/-- The mirror's number of a theorem's object variables. -/
@[simp] theorem thArity_eq (a : Internal.Thm) :
    «Derivation.thArity» (encThm a) = leaf a.arity := rfl

/-- The mirror's context of a theorem. -/
@[simp] theorem thCtx_eq (a : Internal.Thm) : «Derivation.thCtx» (encThm a) = a.ctx := by
  simp [«Derivation.thCtx», encThm]

/-- The mirror's hypotheses of a theorem. -/
@[simp] theorem thHyps_eq (a : Internal.Thm) :
    «Derivation.thHyps» (encThm a) = a.hyps.map encTerm := by
  simp [«Derivation.thHyps», encThm]

/-- The mirror's conclusion of a theorem. -/
@[simp] theorem thConcl_eq (a : Internal.Thm) :
    «Derivation.thConcl» (encThm a) = encTerm a.concl := rfl

/-- The mirror's theorem of its arity, context, hypotheses and conclusion. -/
@[simp] theorem mkThm_eq (a : Internal.Thm) :
    «Derivation.mkThm» (leaf a.arity) (RoseTree.node 0 a.ctx)
      (RoseTree.node 0 (a.hyps.map encTerm)) (encTerm a.concl) = encThm a := rfl

/-- The positions of two lists of one length, each with the elements there, are their pairs. -/
theorem range_all_zip {α β : Type} (p : α → β → Bool) (dx : α) (dy : β) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (List.range xs.length).all (fun i ↦ p (xs.getD i dx) (ys.getD i dy)) =
        (xs.zip ys).all fun q ↦ p q.1 q.2 :=
  List.rec (fun _ _ ↦ rfl) fun x xs ih ys h ↦ by
    rcases ys with _ | ⟨y, ys⟩
    · exact absurd h (Nat.add_one_ne_zero _)
    · simp only [List.length_cons, List.range_succ_eq_map, List.all_cons, List.all_map,
        Function.comp_def, List.getD_cons_zero, List.getD_cons_succ, List.zip_cons_cons]
      rw [ih ys (Nat.succ_inj.mp h)]

/-- The mirror's conjunction with a false truth value first. -/
@[simp] theorem and_false_left (x : Tree) :
    «Prelude.and» (ofBool false) x = ofBool false := rfl

/-- The mirror's test that objects and terms instantiate a theorem in a context. -/
theorem instOk_eq (G : Internal.Globals) (n : ℕ) (Γ : List Tree) (a : Internal.Thm)
    (θ : List Tree) (σ : List Term) :
    «Derivation.instOk» (encGlobals G) (leaf n) Γ (encThm a) θ (σ.map encTerm) =
      ofBool (Internal.instOk G n Γ a θ σ) := by
  simp only [«Derivation.instOk», template, thArity_eq, thCtx_eq, length_eq, List.length_map,
    eq_leaf, allT_isTy, range_eq, Internal.instOk]
  by_cases hl : σ.length = a.ctx.length
  · have hr := allT_map (fun t ↦ Const.equal («Derivation.typeIn» (encGlobals G) (leaf n) Γ
        («Prelude.at» (σ.map encTerm) t))
        («Prelude.some» («PartialHorn.phSubst» θ («Prelude.at» a.ctx t))))
      leaf (fun i ↦ decide (Internal.typeIn G n Γ (σ.getD i Internal.Term.star) =
        some (PartialHorn.subst θ (a.ctx.getD i (leaf 0))))) (List.range σ.length)
      fun i hi ↦ by
        rw [List.mem_range] at hi
        simp only [at_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hl ▸ hi), Option.map_some,
          Option.getD_some, typeIn_eq, phSubst_eq, some_eq, equal_eq, encOpt_inj]
    rw [hr, range_all_zip (fun u A ↦ decide (Internal.typeIn G n Γ u =
      some (PartialHorn.subst θ A))) _ _ σ a.ctx hl, List.zip_map_right, List.all_map]
    simp [hl, Function.comp_def, Bool.and_assoc, beq_eq_decide]
  · have h : (σ.length == a.ctx.length) = false := by simpa using hl
    simp [h, hl]

/-- The mirror's subobject on which arrows into the subobject classifier are truth, with its
inclusion. -/
@[simp] theorem truthSub_eq (X : Tree) (Hs : List Tree) :
    «Derivation.truthSub» X Hs = encPair (Internal.truthSub X Hs) := by
  simp only [«Derivation.truthSub», template, reverse_eq, foldr_eq, List.foldr_reverse, pr_eq,
    mirror_idt, Internal.truthSub]
  exact List.foldl_hom encPair fun _ _ ↦ rfl

/-- The mirror's arrow of a formula in a theorem's context. -/
@[simp] theorem thmArrow_eq (G : Internal.Globals) (a : Internal.Thm) (φ : Term) :
    «Derivation.thmArrow» (encGlobals G) (encThm a) (encTerm φ) = a.arrow G φ := by
  have hc := compile_eq G a.arity φ (Internal.ctxObj a.ctx) (Internal.stdEnv a.ctx)
  simp only [«Derivation.thmArrow», template, thArity_eq, thCtx_eq, ctxObj_eq, stdEnv_eq, hc,
    mapO_eq, getD_eq, mirror_idt, Option.map_map, Internal.Thm.arrow]
  rfl

/-- The mirror's arrow after the inclusion of the subobject of a theorem's hypotheses. -/
@[simp] theorem thmSide_eq (G : Internal.Globals) (a : Internal.Thm) (f : Tree) :
    «Derivation.thmSide» (encGlobals G) (encThm a) f = a.side G f := by
  der_simp [«Derivation.thmSide», Internal.Thm.side, thHyps_eq, thCtx_eq, thmArrow_eq,
    ctxObj_eq, truthSub_eq, mirror_comp, List.isEmpty_iff]

/-- The mirror's sequent of the combinators a theorem compiles to. -/
theorem thmSeq_eq (G : Internal.Globals) (a : Internal.Thm) :
    «Derivation.thmSeq» (encGlobals G) (encThm a) = encSeq (a.seq G) := by
  simp only [«Derivation.thmSeq», template, thConcl_eq, eqParts_eq, Internal.Thm.seq]
  rcases Internal.eqParts a.concl with _ | ⟨t, u⟩ <;>
    der_simp [thmSide_eq, thmArrow_eq, thArity_eq, thCtx_eq, ctxObj_eq, mirror_comp, mirror_tru,
      mirror_bang, «PartialHorn.mkSeq», «PartialHorn.seq», eqn_eq, encSeq,
      List.map_replicate]

/-- The mirror's entry of a theorem of the language. -/
@[simp] theorem entLang_eq (a : Internal.Thm) :
    «Derivation.entLang» (encThm a) = encEntry (.language a) := rfl

/-- The mirror's entry of a sequent of the combinators. -/
@[simp] theorem entComb_eq (s : PartialHorn.Seq) :
    «Derivation.entComb» (encSeq s) = encEntry (.combinators s) := rfl

/-- The mirror's theorem of the language an entry is. -/
@[simp] theorem entryLanguage_eq (e : Internal.Entry) :
    «Derivation.entryLanguage» (encEntry e) = encOpt (e.language?.map encThm) := by
  cases e <;> rfl

/-- The mirror's sequent of the combinators an entry states. -/
@[simp] theorem entrySeq_eq (G : Internal.Globals) (e : Internal.Entry) :
    «Derivation.entrySeq» (encGlobals G) (encEntry e) = encSeq (e.seq G) := by
  cases e with
  | language a => exact thmSeq_eq G a
  | combinators s => rfl

/-- The mirror's test of the compilations of the constants' definitions. -/
theorem anyDefs_eq (G : Internal.Globals) (f : List Tree → Tree)
    (g : List PartialHorn.Defn → Bool) (h : ∀ cds, f (cds.map encDefn) = ofBool (g cds)) :
    «Derivation.anyDefs» (encGlobals G) f = ofBool ((Internal.compileDefs G).any g) := by
  simp only [«Derivation.anyDefs», template, compileDefs_eq]
  cases Internal.compileDefs G <;> mirror_simp [h, Option.any_some]
  rfl

/-- The mirror's test that a certificate proves a sequent. -/
theorem certifies_eq (G : Internal.Globals) (E : Array Internal.Entry) (c : Tree)
    (s : PartialHorn.Seq) :
    «Derivation.certifies» (encGlobals G) (E.toList.map encEntry) c (encSeq s) =
      ofBool (Internal.certifies G E c s) := by
  simp only [«Derivation.certifies», template, Internal.certifies]
  refine anyDefs_eq G _ _ fun cds ↦ ?_
  have hE : (E.toList.map encEntry).map («Derivation.entrySeq» (encGlobals G)) =
      (E.map (Internal.Entry.seq G)).toList.map encSeq := by
    simp [Function.comp_def]
  have hc := pcheck_eq (ext cds) (E.map (Internal.Entry.seq G)) c s.ctx s.hyps
  mirror_simp [ext_eq, mapT_eq, hE, seqCtx_eq, seqHyps_eq, seqConcl_eq, hc, gBase_eq, sig_eq,
    some_eq]
  simp only [show encOpt (some (encEqn s.concl)) = encOpt ((some s.concl).map encEqn) from rfl,
    encOptEqn_inj.eq_iff]
  by_cases h : G.base = sig.length <;> simp [h, ofBool_false]

/-- A context with hypotheses as the pair of the node of its types and the node of its encoded
hypotheses. -/
def encCtx (p : List Tree × List Term) : Tree :=
  encPair (RoseTree.node 0 p.1, RoseTree.node 0 (p.2.map encTerm))

/-- The mirror's context with hypotheses. -/
@[simp] theorem ctxPair_eq (Γ : List Tree) (Φ : List Term) :
    «Derivation.ctxPair» Γ (Φ.map encTerm) = encCtx (Γ, Φ) := rfl

/-- A case analysis of an option into encoded optional trees is the encoding of its binding. -/
@[simp] theorem elim_encOpt {α : Type} (o : Option α) (f : α → Option Tree) :
    o.elim (encOpt none) (fun x ↦ encOpt (f x)) = encOpt (o.bind f) := by
  cases o <;> rfl

/-- The mirror's contexts and hypotheses of a node's children. -/
theorem childCtxs_eq (G : Internal.Globals) (n : ℕ) (l : Label) (ts : List Term)
    (Γ : List Tree) (Φ : List Term) :
    «Derivation.childCtxs» (encGlobals G) (leaf n) (encTerm (RoseTree.node l ts)) Γ
        (Φ.map encTerm) =
      encOpt ((Internal.childCtxs G n l ts Γ Φ).map fun cs ↦ RoseTree.node 0 (cs.map encCtx)) := by
  cases l <;> rcases ts with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, ts⟩⟩⟩⟩ <;>
    der_simp [«Derivation.childCtxs», Internal.childCtxs, labelData,
      «Derivation.ctxPair», encCtx, typeIn_eq, weaken1_eq, weaken2_eq, funext listPart_eq,
      funext roseLabel_eq, elim_encOpt, «Theory.l2», «Theory.l3»,
      mirror_prod, mirror_list, Option.bind_assoc, Option.bind_map]

/-- The mirror's test that a node's child of an index is in the node's context. -/
theorem sameCtx_eq (l : Label) (i : ℕ) :
    «Derivation.sameCtx» (leaf (labelData l).1) (leaf i) =
      ofBool (Internal.sameCtx l i) := by
  cases l <;> der_simp [«Derivation.sameCtx», Internal.sameCtx, labelData] <;> rfl

/-- A rule's position is zero exactly for the identity rewriting. -/
theorem ruleData_eq_zero (r : Internal.Rule) : ((ruleData r).1 == 0) = r.isRefl := by
  cases r <;> rfl

/-- The mirror's test at every position of a list of derivations, the positions' leaves. -/
theorem allT_range_zipIdx (ds : List Internal.Deriv) (F : Tree → Tree)
    (q : ℕ → Tree → Bool) (h : ∀ i, F (leaf i) = ofBool (q i ((ds.map encDeriv).getD i (leaf 0)))) :
    «Base.allT» F ((List.range ds.length).map leaf) =
      ofBool (ds.zipIdx.all fun p ↦ q p.2 (encDeriv p.1)) := by
  rw [allT_map F leaf (fun i ↦ q i ((ds.map encDeriv).getD i (leaf 0))) _ fun i _ ↦ h i]
  congr 1
  simpa [List.all_map, Function.comp_def] using
    congrArg (List.all · id) (range_getD_eq ds encDeriv (leaf 0) q)

/-- The label of an encoded derivation. -/
@[simp] theorem label_encDeriv (d : Internal.Deriv) :
    (encDeriv d).label = (ruleData d.label).1 := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, d = RoseTree.node l cs :=
    ⟨d.label, d.children, (RoseTree.node_label_children d).symm⟩
  simp [encDeriv]

/-- The mirror's contexts in which a congruence rewrites a node's children. -/
theorem congCtxs_eq (G : Internal.Globals) (n : ℕ) (l : Label) (ts : List Term)
    (Γ : List Tree) (Φ : List Term) (ds : List Internal.Deriv) :
    «Derivation.congCtxs» (encGlobals G) (leaf n) (encTerm (RoseTree.node l ts)) Γ
        (Φ.map encTerm) (ds.map encDeriv) =
      encOpt ((Internal.congCtxs G n l ts Γ Φ ds).map fun cs ↦
        RoseTree.node 0 (cs.map encCtx)) := by
  simp only [«Derivation.congCtxs», template, length_eq, List.length_map, range_eq]
  rw [allT_range_zipIdx ds _ (fun i t ↦ Internal.sameCtx l i || t.label == 0) fun i ↦ by
    der_simp [sameCtx_eq, at_eq]]
  simp only [label_encDeriv, ruleData_eq_zero, childCtxs_eq, Internal.congCtxs]
  der_simp [ctxPair_eq]
  split_ifs <;> der_simp [ctxPair_eq]

/-- A rose tree is the node of its label over its children. -/
theorem exists_node {L : Type} (t : RoseTree L) : ∃ l cs, t = RoseTree.node l cs :=
  ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩

/-- The mirror's substitution of a term for the innermost variable of an encoded term. -/
@[simp] theorem subst_instVar (b u : Term) :
    «Language.subst» (encTerm b) («Derivation.instVar» (encTerm u)) =
      encTerm (Internal.Term.subst b (Internal.instVar u)) :=
  subst_eq _ _ _ (instVar_eq u)

/-- The mirror's substitution of two terms for the two innermost variables of an encoded term. -/
@[simp] theorem subst_instVar2 (b u v : Term) :
    «Language.subst» (encTerm b) («Derivation.instVar2» (encTerm u) (encTerm v)) =
      encTerm (Internal.Term.subst b (Internal.instVar2 u v)) :=
  subst_eq _ _ _ (instVar2_eq u v)

/-- The mirror's substitution of a term for the innermost variable, the others in place. -/
@[simp] theorem subst_atVar0 (b u : Term) :
    «Language.subst» (encTerm b) («Derivation.atVar0» (encTerm u)) =
      encTerm (Internal.Term.subst b (Internal.atVar0 u)) :=
  subst_eq _ _ _ (atVar0_eq u)

/-- The mirror's substitution of a list of encoded terms for the variables. -/
@[simp] theorem subst_substList (b : Term) (us : List Term) :
    «Language.subst» (encTerm b) («Language.substList» (us.map encTerm)) =
      encTerm (Internal.Term.subst b (Internal.Term.substList us)) :=
  subst_eq _ _ _ (substList_eq us)

variable (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ) (Γ : List Tree)
  (Φ : List Term)

/-- The mirror's rewriting of an encoded term by beta. -/
theorem rootBeta_eq (t : Term) :
    «Derivation.rootBeta» (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ .beta t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootBeta», Internal.rootStep, labelData]
  rcases cs with _ | ⟨f, _ | ⟨u, _ | ⟨w, cs⟩⟩⟩ <;> der_simp []
  obtain ⟨fl, fs, rfl⟩ := exists_node f
  cases fl <;> der_simp [labelData]
  rcases fs with _ | ⟨b, _ | ⟨b', fs⟩⟩ <;> der_simp [subst_instVar]

/-- The mirror's rewriting of an encoded term by the first component of a pair. -/
theorem rootFst_eq (t : Term) :
    «Derivation.rootFst» (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ .fstPair t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootFst», Internal.rootStep, labelData]
  rcases cs with _ | ⟨p, _ | ⟨u, cs⟩⟩ <;> der_simp []
  obtain ⟨pl, ps, rfl⟩ := exists_node p
  cases pl <;> der_simp [labelData]
  rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, ps⟩⟩⟩ <;> der_simp []

/-- The mirror's rewriting of an encoded term by the second component of a pair. -/
theorem rootSnd_eq (t : Term) :
    «Derivation.rootSnd» (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ .sndPair t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootSnd», Internal.rootStep, labelData]
  rcases cs with _ | ⟨p, _ | ⟨u, cs⟩⟩ <;> der_simp []
  obtain ⟨pl, ps, rfl⟩ := exists_node p
  cases pl <;> der_simp [labelData]
  rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, ps⟩⟩⟩ <;> der_simp []

/-- The mirror's rewriting of an encoded term by the eta of pairs. -/
theorem rootPairEta_eq (t : Term) :
    «Derivation.rootPairEta» (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ .pairEta t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootPairEta», Internal.rootStep, labelData]
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩ <;> der_simp []
  obtain ⟨al, as, rfl⟩ := exists_node a
  obtain ⟨bl, bs, rfl⟩ := exists_node b
  cases al <;> der_simp [labelData]
  rcases as with _ | ⟨p, _ | ⟨p', as⟩⟩ <;> der_simp []
  cases bl <;> der_simp [labelData]
  rcases bs with _ | ⟨q, _ | ⟨q', bs⟩⟩ <;> der_simp [encTerm_eq_iff]
  split_ifs <;> rfl

/-- The mirror's rewriting of an encoded term by the eta of the terminal type. -/
theorem rootUnitEta_eq (t : Term) :
    «Derivation.rootUnitEta» (encGlobals G) (leaf n) Γ (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ .unitEta t).map encTerm) := by
  der_simp [«Derivation.rootUnitEta», Internal.rootStep, typeIn_eq, encOpt_inj,
    mirror_one, equal_eq]
  split_ifs <;> rfl

/-- The mirror's rewriting of an encoded term by the unfolding of a definition. -/
theorem rootDelta_eq (t : Term) :
    «Derivation.rootDelta» (encGlobals G) (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ .delta t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootDelta», Internal.rootStep, labelData]
  rename_i k θ
  rcases hk : G.defs[k]? with _ | (d | ⟨m, b⟩) <;>
    der_simp [gDefs_eq, hk, defLanguage_eq, Internal.Definition.language?, ldBody_eq,
      osubst_eq, subst_substList, mapO_eq]

/-- The mirror's rewriting of an encoded term by the fold of the natural numbers at zero. -/
theorem rootNatZero_eq (kz : ℕ) (t : Term) :
    «Derivation.rootNat» (encGlobals G) (leaf 9) [leaf kz] (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ (.natZero kz) t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootNat», Internal.rootStep, labelData]
  rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> der_simp []
  obtain ⟨ml, ms, rfl⟩ := exists_node m
  cases ml <;> der_simp [labelData]
  rename_i k θ
  rcases θ with _ | ⟨x, θ⟩ <;> rcases ms with _ | ⟨c, _ | ⟨c', ms⟩⟩ <;>
    der_simp [primIs_eq, zeroPrim_eq, encTerm_eq_iff]
  split_ifs <;> simp_all

/-- The mirror's rewriting of an encoded term by the fold of the natural numbers at a
successor. -/
theorem rootNatSucc_eq (ks : ℕ) (t : Term) :
    «Derivation.rootNat» (encGlobals G) (leaf 10) [leaf ks] (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ (.natSucc ks) t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootNat», Internal.rootStep, labelData]
  rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> der_simp []
  obtain ⟨ml, ms, rfl⟩ := exists_node m
  cases ml <;> der_simp [labelData]
  rename_i k θ
  rcases θ with _ | ⟨x, θ⟩ <;> rcases ms with _ | ⟨c, _ | ⟨c', ms⟩⟩ <;>
    der_simp [primIs_eq, succPrim_eq, subst_instVar]
  split_ifs <;> simp_all

/-- The mirror's rewriting of an encoded term by the fold of lists at the empty list. -/
theorem rootListNil_eq (kn : ℕ) (t : Term) :
    «Derivation.rootListNil» (encGlobals G) [leaf kn] (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ (.listNil kn) t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootListNil», Internal.rootStep, labelData]
  rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> der_simp []
  obtain ⟨ml, ms, rfl⟩ := exists_node m
  cases ml <;> der_simp [labelData]
  rename_i k θ
  rcases θ with _ | ⟨x, _ | ⟨y, θ⟩⟩ <;> rcases ms with _ | ⟨c, _ | ⟨c', ms⟩⟩ <;>
    der_simp [primIs_eq, nilPrim_eq, encTerm_eq_iff]
  split_ifs <;> simp_all

/-- The mirror's rewriting of an encoded term by the fold of lists at a construction. -/
theorem rootListCons_eq (kc : ℕ) (t : Term) :
    «Derivation.rootListCons» (encGlobals G) [leaf kc] (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ (.listCons kc) t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootListCons», Internal.rootStep, labelData]
  rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> der_simp []
  obtain ⟨ml, ms, rfl⟩ := exists_node m
  cases ml <;> der_simp [labelData]
  rename_i k θ
  rcases θ with _ | ⟨x, _ | ⟨y, θ⟩⟩ <;> rcases ms with _ | ⟨p, _ | ⟨p', ms⟩⟩ <;> der_simp []
  obtain ⟨pl, ps, rfl⟩ := exists_node p
  cases pl <;> der_simp [labelData]
  rcases ps with _ | ⟨h, _ | ⟨tl, _ | ⟨w', ps⟩⟩⟩ <;>
    der_simp [primIs_eq, consPrim_eq, subst_instVar2]
  split_ifs <;> simp_all

/-- The mirror's rewriting of an encoded term by the fold of rose trees at a construction. -/
theorem rootRoseNode_eq (kn kl kc : ℕ) (t : Term) :
    «Derivation.rootRoseNode» (encGlobals G) [leaf kn, leaf kl, leaf kc] (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ (.roseNode kn kl kc) t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootRoseNode», Internal.rootStep, labelData]
  rcases cs with _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩ <;> der_simp []
  obtain ⟨ml, ms, rfl⟩ := exists_node m
  cases ml <;> der_simp [labelData]
  rcases ms with _ | ⟨p, _ | ⟨p', ms⟩⟩ <;> der_simp []
  obtain ⟨pl, ps, rfl⟩ := exists_node p
  cases pl <;> der_simp [labelData]
  rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨w', ps⟩⟩⟩ <;>
    der_simp [primIs_eq, nodePrim_eq, lnodePrim_eq, nilPrim_eq, consPrim_eq, subst_instVar]
  split_ifs <;> simp_all

/-- The mirror's rewriting of an encoded term by the case analysis of a left injection. -/
theorem rootCaseInl_eq (kc kl : ℕ) (t : Term) :
    «Derivation.rootCase» (encGlobals G) «Derivation.inlPrim» (leaf 0)
        [leaf kc, leaf kl] (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ (.caseInl kc kl) t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootCase», Internal.rootStep, labelData]
  rcases cs with _ | ⟨f, _ | ⟨u, _ | ⟨w, cs⟩⟩⟩ <;> der_simp []
  obtain ⟨fl, fs, rfl⟩ := exists_node f
  cases fl <;> der_simp [labelData]
  rcases fs with _ | ⟨p, _ | ⟨p', fs⟩⟩ <;> der_simp []
  obtain ⟨ul, us, rfl⟩ := exists_node u
  cases ul <;> der_simp [labelData]
  rcases us with _ | ⟨v, _ | ⟨v', us⟩⟩ <;> der_simp []
  obtain ⟨pl, ps, rfl⟩ := exists_node p
  cases pl <;> der_simp [labelData]
  rcases ps with _ | ⟨g, _ | ⟨h, _ | ⟨w', ps⟩⟩⟩ <;>
    der_simp [primIs_eq, casePrim_eq, inlPrim_eq]
  split_ifs <;> simp_all

/-- The mirror's rewriting of an encoded term by the case analysis of a right injection. -/
theorem rootCaseInr_eq (kc kr : ℕ) (t : Term) :
    «Derivation.rootCase» (encGlobals G) «Derivation.inrPrim» (leaf 1)
        [leaf kc, leaf kr] (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ (.caseInr kc kr) t).map encTerm) := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> der_simp [«Derivation.rootCase», Internal.rootStep, labelData]
  rcases cs with _ | ⟨f, _ | ⟨u, _ | ⟨w, cs⟩⟩⟩ <;> der_simp []
  obtain ⟨fl, fs, rfl⟩ := exists_node f
  cases fl <;> der_simp [labelData]
  rcases fs with _ | ⟨p, _ | ⟨p', fs⟩⟩ <;> der_simp []
  obtain ⟨ul, us, rfl⟩ := exists_node u
  cases ul <;> der_simp [labelData]
  rcases us with _ | ⟨v, _ | ⟨v', us⟩⟩ <;> der_simp []
  obtain ⟨pl, ps, rfl⟩ := exists_node p
  cases pl <;> der_simp [labelData]
  rcases ps with _ | ⟨g, _ | ⟨h, _ | ⟨w', ps⟩⟩⟩ <;>
    der_simp [primIs_eq, casePrim_eq, inrPrim_eq]
  split_ifs <;> simp_all

/-- The mirror's rewriting of an encoded term by an equation among the hypotheses. -/
theorem rootHyp_eq (i : ℕ) (flip : Bool) (t : Term) :
    «Derivation.rootHyp» (Φ.map encTerm) [leaf i, ofBool flip] (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ (.rwHyp i flip) t).map encTerm) := by
  simp only [«Derivation.rootHyp», template, Internal.rootStep, at_eq, List.getD_cons_zero,
    List.getD_cons_succ, nth_eq, List.getElem?_map]
  rcases Φ[i]? with _ | φ
  · der_simp []
  · rcases h : Internal.eqParts φ with _ | ⟨a, b⟩ <;> cases flip <;>
      der_simp [eqParts_eq, h, encTerm_eq_iff] <;> split_ifs <;> rfl

/-- The mirror's rewriting of an encoded term by an equational theorem. -/
theorem rootThm_eq (j : ℕ) (θ : List Tree) (σ : List Term) (flip : Bool) (t : Term) :
    «Derivation.rootThm» (encGlobals G) (E.toList.map encEntry) (leaf n) Γ
        [leaf j, RoseTree.node 0 θ, RoseTree.node 0 (σ.map encTerm), ofBool flip] (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ (.thm j θ σ flip) t).map encTerm) := by
  simp only [«Derivation.rootThm», template, Internal.rootStep, at_eq, List.getD_cons_zero,
    List.getD_cons_succ, nth_eq, List.getElem?_map, Array.getElem?_toList, children_eq,
    RoseTree.children_node]
  rcases E[j]? with _ | (a | s)
  · der_simp []
  · by_cases hh : a.hyps = []
    · rcases h : Internal.eqParts a.concl with _ | ⟨u, v⟩ <;> cases flip <;>
        der_simp [entryLanguage_eq, Internal.Entry.language?, thHyps_eq, thConcl_eq, hh,
          eqParts_eq, h, instOk_eq, instTerm_eq, encTerm_eq_iff] <;> split_ifs <;> rfl
    · der_simp [entryLanguage_eq, Internal.Entry.language?, thHyps_eq, hh, List.isEmpty_iff,
        List.map_eq_nil_iff]
  · der_simp [entryLanguage_eq, Internal.Entry.language?]

/-- The mirror's rewriting of an encoded term at its root by a rule. -/
theorem rootStep_eq (l : Internal.Rule) (t : Term) :
    «Derivation.rootStep» (encGlobals G) (E.toList.map encEntry) (leaf n) Γ
        (Φ.map encTerm) (leaf (ruleData l).1) (ruleData l).2 (encTerm t) =
      encOpt ((Internal.rootStep G E n Γ Φ l t).map encTerm) := by
  cases l <;>
    der_simp [«Derivation.rootStep», ruleData, rootBeta_eq G E n Γ Φ,
      rootFst_eq G E n Γ Φ, rootSnd_eq G E n Γ Φ, rootPairEta_eq G E n Γ Φ,
      rootUnitEta_eq G E n Γ Φ, rootDelta_eq G E n Γ Φ, rootNatZero_eq G E n Γ Φ,
      rootNatSucc_eq G E n Γ Φ, rootListNil_eq G E n Γ Φ, rootListCons_eq G E n Γ Φ,
      rootRoseNode_eq G E n Γ Φ, rootCaseInl_eq G E n Γ Φ, rootCaseInr_eq G E n Γ Φ,
      rootThm_eq G E n Γ Φ, rootHyp_eq G E n Γ Φ]
  all_goals rfl

/-- The mirror's rewriting and proving of a derivation, each a function of a context,
hypotheses and a term. -/
abbrev DV : Type :=
  (List Tree → List Tree → Tree → Tree) × (List Tree → List Tree → Tree → Tree)

/-- The mirror's derivation checker's results and the checker's are related when they agree at
every context and every encoded list of hypotheses and term. -/
def DRel (v : DV) (w : Internal.Checks) : Prop :=
  (∀ Γ Φ t, v.1 Γ (Φ.map encTerm) (encTerm t) = encOpt ((w.1 Γ Φ t).map encTerm)) ∧
    ∀ Γ Φ φ, v.2 Γ (Φ.map encTerm) (encTerm φ) = ofBool (w.2 Γ Φ φ)

/-- The derivations of a list of derivations with their results. -/
@[simp] theorem dpTrees_eq (rs : List (Tree × DV)) :
    «Derivation.dpTrees» rs = rs.map Prod.fst :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«Derivation.dpTrees», template, foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- A list of derivations with their results without its head. -/
@[simp] theorem dpTail_eq (rs : List (Tree × DV)) : «Derivation/DPs.tail» rs = rs.tail := by
  cases rs <;> rfl

/-- Dropping the head of a list of derivations with their results as many times as a label. -/
theorem repeat_dpTail (rs : List (Tree × DV)) :
    ∀ i : ℕ, Nat.repeat «Derivation/DPs.tail» i rs = rs.drop i :=
  Nat.rec rfl fun i ih ↦ by rw [Nat.repeat, ih, dpTail_eq, List.tail_drop]

/-- The results of a derivation at a position, none and false out of range. -/
@[simp] theorem dpAt_eq (rs : List (Tree × DV)) (i : ℕ) :
    «Derivation.dpAt» rs (leaf i) = (rs[i]?.map Prod.snd).getD
      (fun _ _ _ ↦ «Prelude.none», fun _ _ _ ↦ leaf 0) := by
  simp only [«Derivation.dpAt», template, iter_leaf, repeat_dpTail]
  cases h : rs.drop i with
  | nil =>
    rw [List.drop_eq_nil_iff] at h
    rw [List.getElem?_eq_none h]
    rfl
  | cons r rest =>
    have : rs[i]? = some r := by
      rw [← List.head?_drop, h]
      rfl
    rw [this]
    rfl

/-- The rewriting of a derivation at a position. -/
@[simp] theorem rw_eq (rs : List (Tree × DV)) (i : ℕ) :
    «Derivation.rw» rs (leaf i) = («Derivation.dpAt» rs (leaf i)).1 := rfl

/-- The proving of a derivation at a position. -/
@[simp] theorem pf_eq (rs : List (Tree × DV)) (i : ℕ) :
    «Derivation.pf» rs (leaf i) = («Derivation.dpAt» rs (leaf i)).2 := rfl

/-- The mirror's map at the positions of a list is the list's map, where the two agree at each
position. -/
theorem mapT_range {β : Type} (F : Tree → Tree) (xs : List β) (g : β → Tree)
    (hF : ∀ i (hi : i < xs.length), F (leaf i) = g xs[i]) :
    «Base.mapT» F ((List.range xs.length).map leaf) = xs.map g := by
  rw [mapT_eq, List.map_map]
  refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
  exact hF i (by simpa using h₂)

/-- A map at the positions of a list is the list's map, where the two agree at each position. -/
theorem map_range_eq {β γ : Type} (F : ℕ → γ) (ys : List β) (g : β → γ)
    (h : ∀ i (hi : i < ys.length), F i = g ys[i]) : (List.range ys.length).map F = ys.map g :=
  List.ext_getElem (by simp) fun i h₁ h₂ ↦ by
    simp only [List.getElem_map, List.getElem_range]
    exact h i (by simpa using h₂)

/-- The checker's rewriting at a rule other than the identity, transitivity and congruence is
its rewriting at the root where the node has no premises. -/
theorem checkStep_root (l : Internal.Rule) (hr : l ≠ .refl) (ht : l ≠ .trans) (hc : l ≠ .cong)
    (cs : List (Internal.Deriv × Internal.Checks)) (t : Term) :
    (Internal.checkStep G E n l cs).1 Γ Φ t =
      if cs = [] then Internal.rootStep G E n Γ Φ l t else none := by
  cases l <;> first | exact absurd rfl hr | exact absurd rfl ht | exact absurd rfl hc |
    rcases cs with _ | ⟨c, cs⟩ <;> rfl

/-- The positions of the rules other than the identity, transitivity and congruence are at least
three. -/
theorem three_le_ruleData (l : Internal.Rule) (hr : l ≠ .refl) (ht : l ≠ .trans)
    (hc : l ≠ .cong) : 3 ≤ (ruleData l).1 := by
  cases l <;> first | exact absurd rfl hr | exact absurd rfl ht | exact absurd rfl hc |
    simp [ruleData]

/-- The mirror's rewriting step at an encoded node of a rule, from its children's results
related to the checker's. -/
theorem rewriteStep_eq (l : Internal.Rule) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (t : Term) :
    «Derivation.rewriteStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData l).1) (ruleData l).2 (xs.map fun x ↦ encDeriv x.1)
        (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ (Φ.map encTerm) (encTerm t) =
      encOpt (((Internal.checkStep G E n l (xs.map fun x ↦ (x.1, x.2.2))).1 Γ Φ t).map
        encTerm) := by
  have h1 : ∀ x ∈ xs, ∀ Γ Φ t, x.2.1.1 Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((x.2.2.1 Γ Φ t).map encTerm) := fun x h ↦ (hx x h).1
  simp only [«Derivation.rewriteStep», template, rootStep_eq G E n Γ Φ l t]
  -- the rules have no decidable equality, but the tests against a constructor are decidable
  have : Decidable (l = .refl) := by cases l <;> first | exact isTrue rfl | exact isFalse nofun
  have : Decidable (l = .trans) := by cases l <;> first | exact isTrue rfl | exact isFalse nofun
  have : Decidable (l = .cong) := by cases l <;> first | exact isTrue rfl | exact isFalse nofun
  by_cases hr : l = .refl
  · subst hr
    rcases xs with _ | ⟨x0, xs⟩ <;> der_simp [ruleData, Internal.checkStep]
  by_cases ht : l = .trans
  · subst ht
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;>
      der_simp [ruleData, Internal.checkStep, h1, Option.map_bind, elim_encOpt, rw_eq, dpAt_eq,
        List.mem_cons, List.mem_singleton, true_or, or_true]
  by_cases hc : l = .cong
  · subst hc
    obtain ⟨lab, us, rfl⟩ := exists_node t
    have hd : (xs.map fun x ↦ encDeriv x.1) = (xs.map Prod.fst).map encDeriv := by simp
    rw [hd, congCtxs_eq]
    der_simp [ruleData, Internal.checkStep, List.map_map, Function.comp_def]
    rcases hΓ : Internal.congCtxs G n lab us Γ Φ (xs.map Prod.fst) with _ | Γs
    · der_simp []
    · simp only [Option.elim_some, Option.bind_some]
      by_cases hl : xs.length = us.length ∧ Γs.length = us.length
      · have hlen : (xs.zip (Γs.zip us)).length = xs.length := by simp [hl.1, hl.2]
        simp only [ite_eq_left_of_eq_true _ _ (eq_true hl)]
        rw [← hlen, map_range_eq _ (xs.zip (Γs.zip us))
          (fun q ↦ encOpt ((q.1.2.2.1 q.2.1.1 q.2.1.2 q.2.2).map encTerm)) fun i hi ↦ ?_]
        · rw [allSomeT_eq, mapM_map_option, List.zip_map_left, List.mapM_map]
          simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id]
          cases (xs.zip (Γs.zip us)).mapM fun q ↦ q.1.2.2.1 q.2.1.1 q.2.1.2 q.2.2 <;>
            der_simp [encTerm_node, mapO_eq, child_node]
        · have hxi : i < xs.length := by simpa [hlen] using hi
          have hΓi : i < Γs.length := by omega
          have hui : i < us.length := by omega
          simp only [List.getElem_zip, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem hΓi, List.getElem?_eq_getElem hui,
            List.getElem?_eq_getElem hxi, Option.map_some, Option.getD_some, rw_eq, dpAt_eq,
            encCtx, scopeCtx_pair, scopeHyps_pair]
          exact h1 _ (List.getElem_mem hxi) _ _ _
      · der_simp [hl]
  have h3 := three_le_ruleData l hr ht hc
  have h0 : (ruleData l).1 ≠ 0 := by omega
  have h1' : (ruleData l).1 ≠ 1 := by omega
  have h2 : (ruleData l).1 ≠ 2 := by omega
  rw [checkStep_root G E n Γ Φ l hr ht hc]
  rcases xs with _ | ⟨x0, xs⟩ <;> der_simp [h0, h1', h2, List.cons_ne_nil]

/-- A test whose negative branch is the leaf of label zero is the conjunction. -/
theorem ite_leaf_zero (P : Prop) [Decidable P] (c : Bool) :
    (if P then ofBool c else leaf 0) = ofBool (decide P && c) := by
  by_cases h : P <;> simp [h, ofBool_false]

/-- Encoded hypotheses followed by an encoded hypothesis are the encoded list. -/
theorem map_append_single {α : Type} (Ψ : List α) (f : α → Term) (ψ : Term) :
    (Ψ.map fun a ↦ encTerm (f a)) ++ [encTerm ψ] = (Ψ.map f ++ [ψ]).map encTerm := by
  simp

/-- An encoded optional term is present with an encoded term exactly when the term is. -/
theorem encOpt_map_eq_some (o : Option Term) (t : Term) :
    (encOpt (o.map encTerm) = encOpt (some (encTerm t))) = (o = some t) := by
  cases o <;> simp [encOpt_inj]

/-- Encoded hypotheses followed by an encoded hypothesis are the encoded list. -/
theorem map_append_single' (Φ : List Term) (ψ : Term) :
    Φ.map encTerm ++ [encTerm ψ] = (Φ ++ [ψ]).map encTerm := by
  simp

/-- The selection of a rule's branch of the mirror's proving step: its tests of the rule's
position and the number of its premises, evaluated. -/
local macro "select_rule" : tactic => `(tactic|
  simp only [ruleData, eq_leaf, length_eq, List.length_map, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, and_eq, and_false_left, Nat.reduceBEq, Bool.and_false,
    Bool.false_and, Bool.and_true, Bool.true_and, label_ne_zero, ofBool_bne, Bool.false_eq_true,
    ↓reduceIte, or_eq, Bool.or_false, Bool.false_or, beq_iff_eq, Nat.reduceEqDiff])

set_option hygiene false in
/-- The simplification of a case of the mirror's proving step: {lit}`der_simp` with the
relations {lit}`h1` and {lit}`h2` of the children's rewriting and proving, their positions, and
the given lemmas. -/
local macro "prove_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (der_simp [ruleData, Internal.checkStep, h1, h2, pf_eq, rw_eq, dpAt_eq, eqParts_eq,
    List.mem_cons, List.mem_singleton, true_or, or_true, encTerm_eq_iff, get_encOpt,
    Option.getD_some, isSome_eq, leaf_zero_eq_ofBool, ite_leaf_zero, map_append_single,
    map_append_single', List.map_id', List.map_id, Bool.decide_eq_true, encOpt_map_eq_some,
    $ls,*]
   try simp only [Bool.and_assoc]))

/-- The children's rewritings related, at hypotheses encoded through any map into terms. -/
theorem rw_rel (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) :
    ∀ x ∈ xs, ∀ {α : Type} (Γ : List Tree) (Ψ : List α) (f : α → Term) (t : Term),
      x.2.1.1 Γ (Ψ.map fun a ↦ encTerm (f a)) (encTerm t) =
        encOpt ((x.2.2.1 Γ (Ψ.map f) t).map encTerm) := fun x h _ Γ Ψ f t ↦ by
  simpa [List.map_map, Function.comp_def] using (hx x h).1 Γ (Ψ.map f) t

/-- The children's provings related, at hypotheses encoded through any map into terms. -/
theorem pf_rel (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) :
    ∀ x ∈ xs, ∀ {α : Type} (Γ : List Tree) (Ψ : List α) (f : α → Term) (φ : Term),
      x.2.1.2 Γ (Ψ.map fun a ↦ encTerm (f a)) (encTerm φ) = ofBool (x.2.2.2 Γ (Ψ.map f) φ) :=
  fun x h _ Γ Ψ f φ ↦ by
    simpa [List.map_map, Function.comp_def] using (hx x h).2 Γ (Ψ.map f) φ

/-- The mirror's proving step at an encoded node of the rule joining two rewritings. -/
theorem proveJoin_eq (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf 18) []
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ (Φ.map encTerm)
        (encTerm φ) =
      ofBool ((Internal.checkStep G E n .join (xs.map fun x ↦ (x.1, x.2.2))).2 Γ Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;> select_rule <;> prove_simp []
  rcases Internal.eqParts φ with _ | ⟨t, u⟩ <;> prove_simp []
  rcases x0.2.2.1 Γ Φ t with _ | v <;> rcases x1.2.2.1 Γ Φ u with _ | v' <;> prove_simp []

/-- The mirror's proving step at an encoded node of the rule of a hypothesis. -/
theorem proveHyp_eq (i : ℕ) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.hyp i)).1) (ruleData (.hyp i)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.hyp i) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, xs⟩ <;> select_rule <;> prove_simp [nth_eq, List.getElem?_map]


/-- The mirror's proving step at an encoded node of the rule of a cut. -/
theorem proveCut_eq (ψ : Term) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.cut ψ)).1) (ruleData (.cut ψ)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.cut ψ) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;> select_rule <;> prove_simp [isFormula_eq]


/-- The mirror's proving step at an encoded node of the rule of a conversion. -/
theorem proveConv_eq (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.conv)).1) (ruleData (.conv)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.conv) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;> select_rule <;> prove_simp []
  rcases x0.2.2.1 Γ Φ φ with _ | ψ <;> prove_simp []


/-- The mirror's proving step at an encoded node of the rule of a conversion from a formula. -/
theorem proveConvFrom_eq (ψ : Term) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.convFrom ψ)).1) (ruleData (.convFrom ψ)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.convFrom ψ) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;> select_rule <;> prove_simp [isFormula_eq]


/-- The mirror's proving step at an encoded node of the rule of propositional extensionality. -/
theorem provePropExt_eq (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.propExt)).1) (ruleData (.propExt)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.propExt) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;> select_rule <;> prove_simp []
  rcases Internal.eqParts φ with _ | ⟨a, b⟩ <;> prove_simp [isFormula_eq]


/-- The mirror's proving step at an encoded node of the rule of function extensionality. -/
theorem proveFunExt_eq (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.funExt)).1) (ruleData (.funExt)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.funExt) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, xs⟩⟩ <;> select_rule <;> prove_simp []
  rcases Internal.eqParts φ with _ | ⟨f, g⟩ <;> prove_simp []
  rcases hT : Internal.typeIn G n Γ f with _ | T <;> prove_simp [typeIn_eq, hT]
  rcases hP : Internal.expParts T with _ | ⟨a, b⟩ <;>
    prove_simp [expParts_eq, hP, weaken1_eq, mVar_eq, mApp_eq, mEq_eq]


/-- The mirror's recognition of a coequalizer's projection. -/
theorem isCoeqProj_eq (p : Internal.Prim) :
    «Derivation.isCoeqProj» (encPrim p) = ofBool p.coeqParts.isSome := by
  obtain ⟨m, a, d, c⟩ := p
  simp only [«Derivation.isCoeqProj», template, prArrow_eq, Internal.Prim.coeqParts]
  obtain ⟨la, as, rfl⟩ := exists_node a
  rcases as with _ | ⟨f, _ | ⟨g, _ | ⟨h, as⟩⟩⟩ <;> der_simp []
  obtain ⟨lf, fs, rfl⟩ := exists_node f
  obtain ⟨lg, gs, rfl⟩ := exists_node g
  rcases fs with _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, fs⟩⟩⟩ <;>
    rcases gs with _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, gs⟩⟩⟩ <;> der_simp [mirror_coeqProj, mirror_comp]
  congr 1
  split_ifs with h
  · simp only [Option.isSome_some, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨decide_eq_true h.1, h.2⟩
  · simp only [Option.isSome_none, Bool.eq_false_iff, ne_eq, Bool.and_eq_true, decide_eq_true_eq]
    exact fun h' ↦ h ⟨of_decide_eq_true h'.1, h'.2⟩

/-- The mirror's relation of a quotient's projection. -/
theorem primRel_eq (p : Internal.Prim) :
    «Derivation.primRel» (encPrim p) = encOpt p.rel? := by
  obtain ⟨m, a, d, c⟩ := p
  simp only [«Derivation.primRel», template, prArrow_eq, prDom_eq, Internal.Prim.rel?]
  obtain ⟨la, as, rfl⟩ := exists_node a
  rcases as with _ | ⟨f, _ | ⟨g, _ | ⟨h, as⟩⟩⟩ <;> der_simp []
  obtain ⟨lf, fs, rfl⟩ := exists_node f
  rcases fs with _ | ⟨f1, _ | ⟨mm, _ | ⟨f3, fs⟩⟩⟩ <;> der_simp []
  obtain ⟨lm, ms, rfl⟩ := exists_node mm
  rcases ms with _ | ⟨r, _ | ⟨r2, _ | ⟨r3, ms⟩⟩⟩ <;>
    der_simp [mirror_coeqProj, «Derivation.relL», «Derivation.relR», mirror_comp,
      mirror_cFst, mirror_cSnd, mirror_truthIncl, Internal.relPair]
  split_ifs <;> simp_all

/-- The mirror's test of the primitive arrows of induction on rose trees. -/
theorem rosePrimsOk_eq (kn kl kc : ℕ) (r a : Tree) :
    «Derivation.rosePrimsOk» (encGlobals G) (leaf kn) (leaf kl) (leaf kc) r a =
      ofBool (decide (((G.prims[kn]? = some Internal.nodePrim ∧ r = rose) ∨
        (G.prims[kn]? = some Internal.lnodePrim ∧ r = lrose a)) ∧
        G.prims[kl]? = some Internal.nilPrim ∧ G.prims[kc]? = some Internal.consPrim)) := by
  simp only [«Derivation.rosePrimsOk», template, primIs_eq, nodePrim_eq, lnodePrim_eq, nilPrim_eq,
    consPrim_eq, mirror_rose, mirror_lrose, equal_eq, and_eq, or_eq]
  congr 1

/-- The mirror's theorem of an arity, a context, hypotheses and a conclusion. -/
@[simp] theorem mkThm_eq' (n : ℕ) (Γ : List Tree) (Φ : List Term) (φ : Term) :
    «Derivation.mkThm» (leaf n) (RoseTree.node 0 Γ) (RoseTree.node 0 (Φ.map encTerm))
      (encTerm φ) = encThm ⟨n, Γ, Φ, φ⟩ := rfl

/-- The mirror's proving step at an encoded node of the rule of induction on the initial object. -/
theorem proveZeroInd_eq (i : ℕ) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.zeroInd i)).1) (ruleData (.zeroInd i)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.zeroInd i) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, xs⟩ <;> select_rule <;>
    prove_simp [nth_eq, isFormula_eq, mirror_cZero, encOpt_inj, Bool.decide_and]


/-- The mirror's proving step at an encoded node of the rule of a certificate of an equation. -/
theorem proveCert_eq (c : Tree) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.cert c)).1) (ruleData (.cert c)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.cert c) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, xs⟩ <;> select_rule <;> prove_simp []
  rcases Internal.eqParts φ with _ | ⟨t, u⟩ <;> prove_simp [compileEq_eq]
  rcases Internal.compileEq G n Γ t u with _ | q <;> prove_simp [certifies_eq]


/-- The mirror's proving step at an encoded node of the rule of a certificate of a theorem's
sequent. -/
theorem proveCertSeq_eq (c : Tree) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.certSeq c)).1) (ruleData (.certSeq c)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.certSeq c) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  have ha := allT_map («Derivation.isFormula» (encGlobals G) (leaf n) Γ) encTerm
    (fun ψ ↦ decide (Internal.typeIn G n Γ ψ = some omega)) Φ fun ψ _ ↦ isFormula_eq G n Γ ψ
  rcases xs with _ | ⟨x0, xs⟩ <;> select_rule <;>
    prove_simp [ha, isFormula_eq, certifies_eq, thmSeq_eq, mkThm_eq', List.all_eq_true]


/-- The mirror's proving step at an encoded node of the rule of induction on the natural numbers
into a hypothesis. -/
theorem proveNatIndHyp_eq (kz ks : ℕ) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.natIndHyp kz ks)).1) (ruleData (.natIndHyp kz ks)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.natIndHyp kz ks) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;> select_rule <;> prove_simp []
  rcases Γ with _ | ⟨c, Γ'⟩ <;> prove_simp []
  rcases hH : Internal.lowerHyps G n Γ' Φ with _ | Φ' <;>
    prove_simp [lowerHyps_eq, hH, primIs_eq, zeroPrim_eq, succPrim_eq, isFormula_eq,
      mirror_nat, equal_eq, subst_instVar, natSuccAt_eq, Bool.decide_and]


/-- The mirror's proving step at an encoded node of the rule of induction on lists into a
hypothesis. -/
theorem proveListIndHyp_eq (kn kc : ℕ) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.listIndHyp kn kc)).1) (ruleData (.listIndHyp kn kc)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.listIndHyp kn kc) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;> select_rule <;> prove_simp []
  rcases Γ with _ | ⟨c, Γ'⟩ <;> prove_simp []
  rcases hl : Internal.listPart c with _ | a <;>
    rcases hH : Internal.lowerHyps G n Γ' Φ with _ | Φ' <;>
    prove_simp [listPart_eq, hl, lowerHyps_eq, hH, primIs_eq, nilPrim_eq, consPrim_eq,
      isFormula_eq, subst_instVar, listConsAt_eq, weaken2_eq, weakenElem_eq, Bool.decide_and]


/-- The mirror's proving step at an encoded node of the rule of induction on a coproduct. -/
theorem proveCoprodInd_eq (kl kr : ℕ) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.coprodInd kl kr)).1) (ruleData (.coprodInd kl kr)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.coprodInd kl kr) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;> select_rule <;> prove_simp []
  rcases Γ with _ | ⟨c, Γ'⟩ <;> prove_simp []
  rcases hp : Internal.coprodParts c with _ | ⟨a, b⟩ <;>
    rcases hH : Internal.lowerHyps G n Γ' Φ with _ | Φ' <;>
    prove_simp [coprodParts_eq, hp, lowerHyps_eq, hH, primIs_eq, inlPrim_eq, inrPrim_eq,
      isFormula_eq, subst_atVar0, «Theory.l2», Bool.decide_and]


/-- The mirror's proving step at an encoded node of the rule of induction on a quotient. -/
theorem proveQuotInd_eq (kq : ℕ) (θ : List Tree) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.quotInd kq θ)).1) (ruleData (.quotInd kq θ)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.quotInd kq θ) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, xs⟩⟩ <;> select_rule <;> prove_simp []
  rcases Γ with _ | ⟨c, Γ'⟩ <;> prove_simp [gPrims_eq, nth_eq, List.getElem?_map]
  rcases hp : G.prims[kq]? with _ | p <;> prove_simp [gPrims_eq, nth_eq, List.getElem?_map, hp]
  rcases hq : p.coeqParts with _ | fg <;> rcases hH : Internal.lowerHyps G n Γ' Φ with _ | Φ' <;>
    prove_simp [isCoeqProj_eq, hq, lowerHyps_eq, hH, allT_isTy, isTy_eq, phSubst_eq, prArity_eq,
      prDom_eq, prCod_eq, isFormula_eq, subst_atVar0, Bool.decide_and]


/-- The mirror's proving step at an encoded node of the rule of induction on the natural numbers. -/
theorem proveNatInd_eq (kz ks : ℕ) (s : Term) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.natInd kz ks s)).1) (ruleData (.natInd kz ks s)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.natInd kz ks s) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, xs⟩⟩⟩⟩ <;> select_rule <;> prove_simp []
  rcases Internal.eqParts φ with _ | ⟨t, u⟩ <;> prove_simp []
  rcases Γ with _ | ⟨c, Γ'⟩ <;> prove_simp []
  rcases hC : Internal.typeIn G n (c :: Γ') t with _ | C <;>
    rcases hH : Internal.lowerHyps G n Γ' Φ with _ | Φ' <;>
    prove_simp [typeIn_eq, hC, lowerHyps_eq, hH, primIs_eq, zeroPrim_eq, succPrim_eq,
      mirror_nat, subst_instVar, subst_atVar0, natSuccAt_eq, encOpt_inj, Bool.decide_and]


/-- The mirror's proving step at an encoded node of the rule of induction on lists. -/
theorem proveListInd_eq (kn kc : ℕ) (s : Term) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.listInd kn kc s)).1) (ruleData (.listInd kn kc s)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.listInd kn kc s) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, xs⟩⟩⟩⟩ <;> select_rule <;> prove_simp []
  rcases Internal.eqParts φ with _ | ⟨t, u⟩ <;> prove_simp []
  rcases Γ with _ | ⟨c, Γ'⟩ <;> prove_simp []
  rcases hC : Internal.typeIn G n (c :: Γ') t with _ | C <;>
    rcases hl : Internal.listPart c with _ | a <;>
    rcases hH : Internal.lowerHyps G n Γ' Φ with _ | Φ' <;>
    prove_simp [typeIn_eq, hC, listPart_eq, hl, lowerHyps_eq, hH, primIs_eq, nilPrim_eq,
      consPrim_eq, subst_instVar, subst_atVar0, listConsAt_eq, weaken2_eq, weakenElem_eq,
      encOpt_inj, Bool.decide_and]


/-- The mirror's proving step at an encoded node of the rule of induction on rose trees. -/
theorem proveRoseInd_eq (kn kl kc : ℕ) (s : Term)
    (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.roseInd kn kl kc s)).1) (ruleData (.roseInd kn kl kc s)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.roseInd kn kl kc s) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  have h3 : ∀ x ∈ xs, ∀ Γ φ, x.2.1.2 Γ [] (encTerm φ) = ofBool (x.2.2.2 Γ [] φ) :=
    fun x h Γ φ ↦ (hx x h).2 Γ [] φ
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;> select_rule <;> prove_simp []
  rcases Internal.eqParts φ with _ | ⟨t, u⟩ <;> prove_simp []
  rcases Γ with _ | ⟨r, _ | ⟨r', Γ⟩⟩ <;> prove_simp []
  rcases hC : Internal.typeIn G n [r] t with _ | C <;>
    rcases hp : Internal.roseParts r with _ | ⟨a, fold⟩ <;>
    prove_simp [h3, typeIn_eq, hC, roseLabel_eq, hp, rosePrimsOk_eq, roseNodeAt_eq,
      roseMapAt_eq, subst_atVar0, mirror_list, «Theory.l2», encOpt_inj,
      Bool.decide_and]


/-- The mirror's proving step at an encoded node of the rule of induction on rose trees into a
hypothesis. -/
theorem proveRoseIndHyp_eq (kn kl kc : ℕ) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.roseIndHyp kn kl kc)).1) (ruleData (.roseIndHyp kn kl kc)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.roseIndHyp kn kl kc) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  have h4 : ∀ x ∈ xs, ∀ Γ ψ φ,
      x.2.1.2 Γ [encTerm ψ] (encTerm φ) = ofBool (x.2.2.2 Γ [ψ] φ) :=
    fun x h Γ ψ φ ↦ (hx x h).2 Γ [ψ] φ
  simp only [«Derivation.proveStep»]
  rcases xs with _ | ⟨x0, _ | ⟨x1, xs⟩⟩ <;> select_rule <;> prove_simp []
  rcases Γ with _ | ⟨r, _ | ⟨r', Γ⟩⟩ <;> prove_simp []
  rcases hp : Internal.roseParts r with _ | ⟨a, fold⟩ <;>
    prove_simp [h4, roseLabel_eq, hp, rosePrimsOk_eq, roseNodeAt_eq, roseHyp_eq, isFormula_eq,
      mirror_list, «Theory.l2», Bool.decide_and]


/-- The mirror's test at the positions of a list is the list's test, where the two agree at each
position. -/
theorem allT_range_eq {β : Type} (F : Tree → Tree) (ys : List β) (g : β → Bool)
    (h : ∀ i (hi : i < ys.length), F (leaf i) = ofBool (g ys[i])) :
    «Base.allT» F ((List.range ys.length).map leaf) = ofBool (ys.all g) := by
  rw [allT_map F leaf (fun i ↦ (ys[i]?.map g).getD true) _ fun i hi ↦ by
    rw [List.mem_range] at hi
    rw [h i hi, List.getElem?_eq_getElem hi]
    rfl]
  congr 1
  simpa [List.all_map, Function.comp_def] using congrArg (List.all · id)
    (map_range_eq (fun i ↦ (ys[i]?.map g).getD true) ys g fun i hi ↦ by
      rw [List.getElem?_eq_getElem hi]
      rfl)

/-- The mirror's proving step at an encoded node of the rule applying a theorem. -/
theorem proveApply_eq (j : ℕ) (θ : List Tree) (σ : List Term)
    (xs : List (Internal.Deriv × DV × Internal.Checks)) (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2)
    (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData (.apply j θ σ)).1) (ruleData (.apply j θ σ)).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n (.apply j θ σ) (xs.map fun x ↦ (x.1, x.2.2))).2 Γ
        Φ φ) := by
  have h1 := rw_rel xs hx
  have h2 := pf_rel xs hx
  have hr : ∀ a : Internal.Thm, xs.length = a.hyps.length →
      «Base.allT» (fun t ↦ «Derivation.pf»
          (xs.map fun x ↦ (encDeriv x.1, x.2.1)) t Γ (Φ.map encTerm)
          («Derivation.instTerm» θ (σ.map encTerm)
            («Prelude.at» («Derivation.thHyps» (encThm a)) t)))
        («Base.range» (leaf xs.length)) =
      ofBool ((xs.zip a.hyps).all fun q ↦ q.1.2.2.2 Γ Φ (Internal.instTerm θ σ q.2)) := by
    intro a hl
    have hz : xs.length = (xs.zip a.hyps).length := by simp [hl]
    simp only [thHyps_eq, range_eq]
    rw [hz]
    refine allT_range_eq _ (xs.zip a.hyps) _ fun i hi ↦ ?_
    have hxi : i < xs.length := by simpa [← hz] using hi
    have hai : i < a.hyps.length := by omega
    simp only [List.getElem_zip, pf_eq, dpAt_eq, at_eq, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem hxi, List.getElem?_eq_getElem hai,
      Option.map_some, Option.getD_some, instTerm_eq]
    exact (hx _ (List.getElem_mem hxi)).2 Γ Φ _
  simp only [«Derivation.proveStep»]
  select_rule
  simp only [template, at_eq, List.getD_cons_zero, List.getD_cons_succ, children_eq,
    RoseTree.children_node, nth_eq, List.getElem?_map, Array.getElem?_toList]
  rcases hE : E[j]? with _ | (a | s)
  · prove_simp [hE]
  · by_cases hl : xs.length = a.hyps.length
    · have hr' := hr a hl
      simp only [thHyps_eq, range_eq, hl] at hr'
      simp only [Option.map_some, bindO_eq, Option.elim_some, entryLanguage_eq,
        Internal.Entry.language?, isSome_eq, Option.isSome_some, 
        ]
      prove_simp [hE, hr', instOk_eq, instTerm_eq, thConcl_eq, thHyps_eq, hl, List.zip_map_left,
        List.all_map, Function.comp_def, Internal.Entry.language?, Prod.map_fst, Prod.map_snd,
        decide_true, Bool.decide_and, id_eq]
    · prove_simp [hE, entryLanguage_eq, Internal.Entry.language?, instOk_eq, instTerm_eq,
        thConcl_eq, thHyps_eq, hl, decide_false, Bool.false_and, Bool.and_false]
  · prove_simp [hE, entryLanguage_eq, Internal.Entry.language?]

/-- The mirror's proving step at an encoded node of a rule, from its children's results related
to the checker's. -/
theorem proveStep_eq (l : Internal.Rule) (xs : List (Internal.Deriv × DV × Internal.Checks))
    (hx : ∀ x ∈ xs, DRel x.2.1 x.2.2) (Γ : List Tree) (φ : Term) :
    «Derivation.proveStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (leaf (ruleData l).1) (ruleData l).2
        (xs.map fun x ↦ encDeriv x.1) (xs.map fun x ↦ (encDeriv x.1, x.2.1)) Γ
        (Φ.map encTerm) (encTerm φ) =
      ofBool ((Internal.checkStep G E n l (xs.map fun x ↦ (x.1, x.2.2))).2 Γ Φ φ) := by
  cases l
  case join => exact proveJoin_eq G E n Φ xs hx Γ φ
  case natInd kz ks s => exact proveNatInd_eq G E n Φ kz ks s xs hx Γ φ
  case listInd kn kc s => exact proveListInd_eq G E n Φ kn kc s xs hx Γ φ
  case hyp i => exact proveHyp_eq G E n Φ i xs hx Γ φ
  case cut ψ => exact proveCut_eq G E n Φ ψ xs hx Γ φ
  case conv => exact proveConv_eq G E n Φ xs hx Γ φ
  case convFrom ψ => exact proveConvFrom_eq G E n Φ ψ xs hx Γ φ
  case propExt => exact provePropExt_eq G E n Φ xs hx Γ φ
  case funExt => exact proveFunExt_eq G E n Φ xs hx Γ φ
  case apply j θ σ => exact proveApply_eq G E n Φ j θ σ xs hx Γ φ
  case natIndHyp kz ks => exact proveNatIndHyp_eq G E n Φ kz ks xs hx Γ φ
  case listIndHyp kn kc => exact proveListIndHyp_eq G E n Φ kn kc xs hx Γ φ
  case cert c => exact proveCert_eq G E n Φ c xs hx Γ φ
  case certSeq c => exact proveCertSeq_eq G E n Φ c xs hx Γ φ
  case roseInd kn kl kc s => exact proveRoseInd_eq G E n Φ kn kl kc s xs hx Γ φ
  case roseIndHyp kn kl kc => exact proveRoseIndHyp_eq G E n Φ kn kl kc xs hx Γ φ
  case coprodInd kl kr => exact proveCoprodInd_eq G E n Φ kl kr xs hx Γ φ
  case zeroInd i => exact proveZeroInd_eq G E n Φ i xs hx Γ φ
  case quotInd kq θ => exact proveQuotInd_eq G E n Φ kq θ xs hx Γ φ
  all_goals
    simp only [«Derivation.proveStep»]
    select_rule
    simp only [leaf_zero_eq_ofBool]
    rfl

/-- The mirror's checker at an encoded derivation is related to the checker at the derivation:
their rewritings and their provings agree at every context and every encoded list of hypotheses
and term. -/
theorem check_eq (d : Internal.Deriv) :
    DRel («Derivation.check» (encGlobals G) (E.toList.map encEntry) (leaf n) (encDeriv d))
      (Internal.check G E n d) :=
  fold_pair_enc (fun r ↦ (ruleData r).1) (fun r ↦ RoseTree.node 0 (ruleData r).2) DRel
    (fun l rs ↦ by simp only [dpTrees_eq]) (Internal.checkStep G E n)
    (fun l v xs hx ↦ ⟨fun Γ Φ t ↦ by
        simp only [dpTrees_eq, dpTail_eq, List.map_cons, List.tail_cons, at_eq,
          List.getD_cons_zero, children_eq, RoseTree.children_node, List.map_map,
          Function.comp_def]
        exact rewriteStep_eq G E n Γ Φ l xs hx t,
      fun Γ Φ φ ↦ by
        simp only [dpTrees_eq, dpTail_eq, List.map_cons, List.tail_cons, at_eq,
          List.getD_cons_zero, children_eq, RoseTree.children_node, List.map_map,
          Function.comp_def]
        exact proveStep_eq G E n Φ l xs hx Γ φ⟩) d

/-- The mirror's test that a derivation proves a theorem. -/
theorem thmChecks_eq (a : Internal.Thm) (d : Internal.Deriv) :
    «Derivation.thmChecks» (encGlobals G) (E.toList.map encEntry) (encThm a) (encDeriv d) =
      ofBool (a.checks G E d) := by
  have hc := (check_eq G E a.arity d).2 a.ctx a.hyps a.concl
  have ha := allT_map («Derivation.isFormula» (encGlobals G) (leaf a.arity) a.ctx) encTerm
    (fun ψ ↦ decide (Internal.typeIn G a.arity a.ctx ψ = some omega)) a.hyps
    fun ψ _ ↦ isFormula_eq G a.arity a.ctx ψ
  der_simp [«Derivation.thmChecks», Internal.Thm.checks, thArity_eq, thCtx_eq, thHyps_eq,
    thConcl_eq, allT_isTy, ha, isFormula_eq, hc, ite_leaf_zero, Bool.decide_eq_true,
    Bool.decide_and]
  simp only [Bool.and_assoc]

/-- The mirror's sequent that a primitive arrow is an arrow from its domain to its codomain. -/
@[simp] theorem primSeq_eq (p : Internal.Prim) :
    «Derivation.primSeq» (encPrim p) = encSeq p.seq := by
  simp [«Derivation.primSeq», «PartialHorn.mkSeq», «PartialHorn.seq»,
    Internal.Prim.seq, encSeq, prArity_eq, prArrow_eq, prDom_eq, prCod_eq, List.map_replicate]

/-- The mirror's confirmation of a primitive arrow. -/
theorem primConfirms_eq (p : Internal.Prim) (c : Option Tree) :
    «Derivation.primConfirms» (encGlobals G) (E.toList.map encEntry) (encPrim p)
        (encOpt c) = ofBool (p.confirms G E c) := by
  cases c with
  | none =>
    der_simp [«Derivation.primConfirms», Internal.Prim.confirms]
    refine anyDefs_eq G _ _ fun cds ↦ ?_
    der_simp [gBase_eq, sig_eq, envOfDefs_eq, primOk_eq, ite_leaf_zero, Bool.decide_eq_true]
  | some c =>
    der_simp [«Derivation.primConfirms», Internal.Prim.confirms]
    rw [anyDefs_eq G _ (fun cds ↦ p.wf G (ext cds).sig) fun cds ↦ by
      der_simp [ext_eq, thySig_eq, primWf_eq]]
    der_simp [certifies_eq, primSeq_eq, ite_leaf_zero, Bool.decide_eq_true]

/-- An encoded optional sort is a given sort exactly when the optional sort is. -/
theorem decide_encOpt_sort (o : Option ℕ) (s : ℕ) :
    decide (encOpt (o.map leaf) = encOpt (some (leaf s))) = (o == some s) := by
  cases o <;> simp [encOpt_inj, leaf_inj, beq_eq_decide]

/-- The mirror's confirmation of an object in object parameters. -/
theorem objConfirms_eq (m : ℕ) (b : Tree) (c : Option Tree) :
    «Derivation.objConfirms» (encGlobals G) (E.toList.map encEntry) (leaf m) b
        (encOpt c) = ofBool (Internal.objConfirms G E m b c) := by
  cases c with
  | none =>
    der_simp [«Derivation.objConfirms», Internal.objConfirms]
    refine anyDefs_eq G _ _ fun cds ↦ ?_
    der_simp [gBase_eq, sig_eq, envOfDefs_eq, objOk_eq, ite_leaf_zero, Bool.decide_eq_true]
  | some c =>
    der_simp [«Derivation.objConfirms», Internal.objConfirms]
    rw [anyDefs_eq G _ (fun cds ↦ PartialHorn.sortOf (ext cds).sig (List.replicate m Sorts.obj) b ==
      some Sorts.obj) fun cds ↦ by
        der_simp [ext_eq, thySig_eq, sortOf_objs, equal_eq, decide_encOpt_sort]]
    have hs : «PartialHorn.mkSeq» (List.replicate m (leaf 0)) [] (encEqn (dfd b)) =
        encSeq ⟨List.replicate m Sorts.obj, [], dfd b⟩ := by
      simp [«PartialHorn.mkSeq», «PartialHorn.seq», encSeq, List.map_replicate]
    der_simp [dfd_eq, hs, certifies_eq, ite_leaf_zero, Bool.decide_eq_true]

/-- The mirror's check of a definition of the language. -/
@[simp] theorem ldChecks_eq (d : Internal.Defn) :
    «Derivation.ldChecks» (encGlobals G) (encLDefn d) = ofBool (d.checks G) := by
  der_simp [«Derivation.ldChecks», Internal.Defn.checks, ldCompile_eq, ldArity_eq,
    ldType_eq, isTy_eq, Option.isSome_map]

/-- The mirror's state of a development. -/
@[simp] theorem devState_eq (s : Internal.Globals × Array Internal.Entry) :
    «Derivation.stateOf» (encGlobals s.1) (s.2.toList.map encEntry) = encState s := rfl

/-- The mirror's constants with new primitive arrows. -/
@[simp] theorem withPrims_eq (ps : List Internal.Prim) :
    «Derivation.withPrims» (encGlobals G) (ps.map encPrim) =
      encGlobals { G with prims := ps } := by
  simp only [«Derivation.withPrims», template, gDefs_eq, gBase_eq, globals_eq]

/-- The mirror's constants with new definitions. -/
@[simp] theorem withDefs_eq (ds : List Internal.Definition) :
    «Derivation.withDefs» (encGlobals G) (ds.map encDefinition) =
      encGlobals { G with defs := ds } := by
  simp only [«Derivation.withDefs», template, gPrims_eq, gBase_eq, globals_eq]

/-- The mirror's list with an element at its end. -/
@[simp] theorem push_eq (xs : List Tree) (x : Tree) :
    «Derivation.push» xs x = xs ++ [x] := by
  simp [«Derivation.push»]

/-- The mirror's test that a term in object parameters is an arrow of the extended signature. -/
theorem sortsArr_eq (m : ℕ) (f : Tree) :
    «Derivation.sortsArr» (encGlobals G) (leaf m) f =
      ofBool ((Internal.compileDefs G).any fun cds ↦
        PartialHorn.sortOf (ext cds).sig (List.replicate m Sorts.obj) f == some Sorts.arr) := by
  rw [«Derivation.sortsArr»]
  exact anyDefs_eq G _ _ fun cds ↦ by
    der_simp [ext_eq, thySig_eq, sortOf_objs, equal_eq, decide_encOpt_sort]

/-- An encoded list with an encoded element at its end is the encoded list. -/
theorem map_push {α : Type} (f : α → Tree) (xs : List α) (x : α) :
    xs.map f ++ [f x] = (xs ++ [x]).map f := by
  simp

/-- The mirror's primitive arrow of its fields. -/
@[simp] theorem primitive_eq (m : ℕ) (f a b : Tree) :
    «Language.primitive» (leaf m) f a b = encPrim ⟨m, f, a, b⟩ := rfl

/-- The mirror's object definition of its fields. -/
@[simp] theorem defObj_eq (m : ℕ) (b : Tree) :
    «Language.defObj» (leaf m) b = encDefinition (.object m b) := rfl

/-- The mirror's theorem of an arity, a context, one hypothesis and a conclusion. -/
@[simp] theorem mkThm_single (n : ℕ) (Γ : List Tree) (ψ φ : Term) :
    «Derivation.mkThm» (leaf n) (RoseTree.node 0 Γ) (RoseTree.node 0 [encTerm ψ])
      (encTerm φ) = encThm ⟨n, Γ, [ψ], φ⟩ := rfl

/-- The mirror's theorem of an arity, a context, no hypotheses and a conclusion. -/
@[simp] theorem mkThm_nil (n : ℕ) (Γ : List Tree) (φ : Term) :
    «Derivation.mkThm» (leaf n) (RoseTree.node 0 Γ) (RoseTree.node 0 []) (encTerm φ) =
      encThm ⟨n, Γ, [], φ⟩ := rfl

/-- The mirror's first component of the node of two trees. -/
@[simp] theorem p1_node (a b : Tree) : «Language.p1» (RoseTree.node 0 [a, b]) = a := rfl

/-- The mirror's second component of the node of two trees. -/
@[simp] theorem p2_node (a b : Tree) : «Language.p2» (RoseTree.node 0 [a, b]) = b := rfl

/-- A test of an encoded tree is the encoding of the test of a value encoding to it. -/
theorem ite_encOpt {α : Type} (P : Prop) {i₁ i₂ : Decidable P} (a : Tree) (x : α)
    (f : α → Tree) (h : a = f x) :
    @ite _ P i₁ (encOpt (some a)) (encOpt none) = encOpt ((@ite _ P i₂ (some x) none).map f) := by
  subst h
  cases i₁ <;> cases i₂ <;> first | rfl | contradiction

/-- The mirror's declaration of the quotient of a type by a relation. -/
theorem quotStep_eq (m : ℕ) (A : Tree) (R : Term) :
    «Derivation.quotStep» (encGlobals G) (E.toList.map encEntry) (leaf m) A (encTerm R) =
      encOpt ((Internal.Decl.step G E (.quotient m A R)).map encState) := by
  have hc := compile_eq G m R (Internal.ctxObj [A, A]) (Internal.stdEnv [A, A])
  simp only [«Derivation.quotStep», template, «Theory.l2», single_eq, ctxObj_eq,
    stdEnv_eq, hc, Internal.Decl.step]
  rcases Internal.compile G m R (Internal.ctxObj [A, A]) (Internal.stdEnv [A, A]) with _ | ⟨r, t⟩
  · der_simp []
  · der_simp [gPrims_eq, gDefs_eq, gBase_eq, sig_eq, objVars_eq, phOp_eq, primitive_eq,
      defObj_eq, mirror_coeqProj, mirror_coeqz, «Derivation.relL»,
      «Derivation.relR», mirror_comp, mirror_cFst, mirror_cSnd, mirror_truthIncl,
      map_push, globals_eq, isTy_eq, scoped_eq, prArrow_eq, prCod_eq, sortsArr_eq,
      isFormula_eq, mkThm_single, thConcl_eq, entLang_eq, «Derivation.stateOf», encState,
      Array.toList_push, mirror_omega, ite_leaf_zero, Internal.relPair, push_eq, encPair, p1_node,
      p2_node]
    refine ite_encOpt _ _ _ _ ?_
    simp [encState, Array.toList_push]

/-- An encoded optional pair is present with an encoded pair exactly when the pair is. -/
theorem encOpt_pair_eq_some (o : Option (Tree × Tree)) (q : Tree × Tree) :
    (encOpt (o.map encPair) = encOpt (some (encPair q))) = (o = some q) := by
  cases o <;> simp [encOpt_inj, encPair_inj]

/-- The mirror's declaration of the descent of a function through a quotient. -/
theorem descStep_eq (kq : ℕ) (C : Tree) (h : Term) (jr : ℕ) :
    «Derivation.descStep» (encGlobals G) (E.toList.map encEntry) (leaf kq) C (encTerm h)
        (leaf jr) = encOpt ((Internal.Decl.step G E (.descent kq C h jr)).map encState) := by
  simp only [«Derivation.descStep», template, Internal.Decl.step, gPrims_eq, nth_eq,
    List.getElem?_map, Array.getElem?_toList]
  rcases hp : G.prims[kq]? with _ | p
  · der_simp []
  rcases hT : E[jr]? with _ | (T | s)
  · der_simp []
  · rcases hr : p.rel? with _ | r
    · der_simp [primRel_eq, hr, entryLanguage_eq, Internal.Entry.language?]
    have hc := compile_eq G p.arity h (Internal.ctxObj [p.dom]) (Internal.stdEnv [p.dom])
    rcases hC : Internal.compile G p.arity h (Internal.ctxObj [p.dom]) (Internal.stdEnv [p.dom])
      with _ | ⟨H, C'⟩
    · der_simp [primRel_eq, hr, entryLanguage_eq, Internal.Entry.language?, prArity_eq,
        prDom_eq, ctxObj_eq, stdEnv_eq, hc, hC]
    obtain ⟨Ta, Tc, Th, Tq⟩ := T
    have hc2 := fun R' ↦
      compile_eq G p.arity R' (Internal.ctxObj [p.dom, p.dom]) (Internal.stdEnv [p.dom, p.dom])
    rcases Th with _ | ⟨R', _ | ⟨R'', Th⟩⟩ <;>
      der_simp [primRel_eq, hr, entryLanguage_eq, Internal.Entry.language?, prArity_eq,
        prDom_eq, prCod_eq, prArrow_eq, ctxObj_eq, stdEnv_eq, hc, hC, hc2, thHyps_eq, thArity_eq,
        thCtx_eq, thConcl_eq, «Theory.l2», primitive_eq, mirror_coeqDesc,
        «Derivation.relL», «Derivation.relR», mirror_comp, mirror_cFst,
        mirror_cSnd, mirror_truthIncl, Internal.relPair, push_eq, map_push, withPrims_eq,
        objVars_eq, weaken1_eq, isTy_eq, scoped_eq, sortsArr_eq, isFormula_eq, mkThm_nil,
        entLang_eq, «Derivation.stateOf», sig_eq, gBase_eq, equalTs_eq,
        encOpt_pair_eq_some, encTerm_eq_iff, mirror_omega, ite_leaf_zero]
    refine ite_encOpt _ _ _ _ ?_
    simp [encState, encPair, Array.toList_push]
  · der_simp [entryLanguage_eq, Internal.Entry.language?]

/-- The mirror's definition of the language as a definition of either kind. -/
@[simp] theorem defLang_eq (d : Internal.Defn) :
    «Language.defLang» (encLDefn d) = encDefinition (.language d) := rfl

/-- The mirror's state after a declaration, where its proof proves it. -/
theorem declStep_eq (d : Internal.Decl) :
    «Derivation.declStep» (encGlobals G) (E.toList.map encEntry) (encDecl d) =
      encOpt ((d.step G E).map encState) := by
  cases d with
  | quotient m A R =>
    simp only [«Derivation.declStep», template, encDecl, Internal.Decl.step] at ⊢
    der_simp []
    exact quotStep_eq G E m A R
  | descent kq C h jr =>
    der_simp [«Derivation.declStep», encDecl]
    exact descStep_eq G E kq C h jr
  | language a dv =>
    der_simp [«Derivation.declStep», encDecl, Internal.Decl.step, thmChecks_eq,
      entLang_eq, push_eq, map_push, «Derivation.stateOf»]
    refine ite_encOpt _ _ _ _ ?_
    simp [encState, encPair, Array.toList_push]
  | combinators s c =>
    der_simp [«Derivation.declStep», encDecl, Internal.Decl.step, certifies_eq,
      entComb_eq, push_eq, map_push, «Derivation.stateOf»]
    refine ite_encOpt _ _ _ _ ?_
    simp [encState, encPair, Array.toList_push]
  | definition df =>
    der_simp [«Derivation.declStep», encDecl, Internal.Decl.step, ldChecks_eq, gDefs_eq,
      defLang_eq, push_eq, map_push, withDefs_eq, «Derivation.stateOf»]
    refine ite_encOpt _ _ _ _ ?_
    simp [encState, encPair]
  | constant p c =>
    der_simp [«Derivation.declStep», encDecl, Internal.Decl.step, primConfirms_eq,
      gPrims_eq, push_eq, map_push, withPrims_eq, «Derivation.stateOf»]
    refine ite_encOpt _ _ _ _ ?_
    simp [encState, encPair]
  | object m b c =>
    der_simp [«Derivation.declStep», encDecl, Internal.Decl.step, objConfirms_eq,
      gDefs_eq, defObj_eq, push_eq, map_push, withDefs_eq, «Derivation.stateOf»]
    refine ite_encOpt _ _ _ _ ?_
    simp [encState, encPair]

/-- The mirror's states after declarations from an optional state, each declaration proved with
those before it. -/
theorem foldl_declStep (ds : List Internal.Decl) :
    ∀ o : Option (Internal.Globals × Array Internal.Entry),
      (ds.map encDecl).foldl (fun st d ↦ «Base.bindO» st fun s ↦
          «Derivation.declStep» («Language.p1» s)
            (Const.children («Language.p2» s)) d) (encOpt (o.map encState)) =
        encOpt ((o.bind fun s ↦ ds.foldlM (fun st d ↦ d.step st.1 st.2) s).map encState) :=
  ds.rec (fun o ↦ by cases o <;> rfl) fun d ds ih o ↦ by
    rw [List.map_cons, List.foldl_cons]
    have hs : «Base.bindO» (encOpt (o.map encState)) (fun s ↦
        «Derivation.declStep» («Language.p1» s)
          (Const.children («Language.p2» s)) (encDecl d)) =
        encOpt ((o.bind fun st ↦ d.step st.1 st.2).map encState) := by
      cases o with
      | none => simp only [Option.map_none, bindO_eq, Option.elim_none, Option.bind_none]
      | some st =>
        simp only [Option.map_some, bindO_eq, Option.elim_some, encState, p1_node, p2_node,
          children_node, declStep_eq, Option.bind_some]
    rw [hs, ih]
    cases o with
    | none => rfl
    | some st =>
      simp only [Option.bind_some, List.foldlM_cons]
      rfl

/-- The mirror's state after a development, each declaration proved with those before it, is the
checker's. -/
theorem checkDev_eq (ds : List Internal.Decl) :
    «Derivation.checkDev» (encGlobals G) (E.toList.map encEntry) (ds.map encDecl) =
      encOpt ((Internal.checkDev G E ds).map encState) := by
  simp only [«Derivation.checkDev», template, reverse_eq, foldr_eq, List.foldr_reverse]
  exact foldl_declStep ds (some (G, E))

end GebTests.Prototypes.FreeTopos.Agreement.Derivation

end
