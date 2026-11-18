/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Prove
public import Geb.Prototypes.FreeTopos.Internal.Provers

set_option doc.verso true in
/-!
# The provers written in Geb

The provers of {lit}`bootstrap/free-topos/prove.geb`, in the Lean the bootstrap compiler emits
({lit}`GebMirror.Metalogic`), agree with the Lean provers of the internal language
({name}`Geb.FreeTopos.Internal.byNorm`) at every encoded input. A prover's proof is a
certificate of the checker with a step of conversion
({name}`Geb.FreeTopos.Internal.ConvDeriv`): a reduction that rewrites is named by the step of
its rules, its fuel and, for a reduction to a depth, its depth, in place of the derivation it
computes, where that derivation has more nodes than a bound
({name}`Geb.FreeTopos.Internal.stepBound`), and keeps the derivation otherwise; a reduction that
does not rewrite is the identity. The mirror's reductions that name steps are the reductions
related in {lit}`GebTests.Prototypes.FreeTopos.Agreement.Prove`, which compute derivations,
followed by that replacement, as {name}`Geb.FreeTopos.Internal.normalizeC` and
{name}`Geb.FreeTopos.Internal.evalC` are, so that the provers written in Geb construct exactly
the certificates the Lean provers construct.

A certificate is encoded as a derivation is, the node of its rule's position over the node of the
rule's data and its premises: a rule of the language at its position and with its data, and the
steps of conversion and the application of a theorem at the positions after the language's rules.
A step names a rule of the normalizer as it is before its preparation: the theorem, for a
prepared theorem, whose matching no tree encodes.

## Main definitions

* {lit}`convData`, {lit}`encConv` — the encoding of a rule of the certificates and of a
  certificate.
* {lit}`encCB`, {lit}`encTCB`, {lit}`encTC` — a reduction's certificate with its mark, a term
  with it, and a term with a certificate.
* {lit}`NRelC`, {lit}`ERelC`, {lit}`PRel` — the relations of the mirror's normalizations,
  reductions to a depth and provers to the provers', at certificates.

## Main statements

* {lit}`ruleNode_eq`, {lit}`rulesNode_eq` — the rules a step names, for related rules.
* {lit}`dSize_eq`, {lit}`stepped_eq` — the number of a derivation's nodes, and a reduction's
  result with the certificate of its rewriting.
* {lit}`normalizeC_eq`, {lit}`evalC_eq` — the reductions that name steps agree.
* {lit}`byNorm_eq`, {lit}`byNormW_eq` — the proofs by normalization, innermost first and through
  weak head normal forms, agree.
* {lit}`byNatInd_eq`, {lit}`byListInd_eq`, {lit}`byNatIndHyp_eq`, {lit}`byListIndHyp_eq`,
  {lit}`byRoseInd_eq` — the proofs by induction, each premise by normalization, agree.
* {lit}`byFunExt_eq`, {lit}`bySplit_eq`, {lit}`byListIndWith_eq`, {lit}`byRoseIndHyp_eq` — the
  proofs of an equation from proofs of others agree at related provers.

## Tags

prover, conversion, internal language, normalization, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Provers

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Fold GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.Language
  GebTests.Prototypes.FreeTopos.Agreement.Derivation
  GebTests.Prototypes.FreeTopos.Agreement.Prove
open Internal (Term Deriv NormRule ConvRule ConvDeriv)
open scoped FinEnum

/-! Certificates. -/

/-- The position of a rule of the certificates, and its data: those of a rule of the language,
and after the language's rules the normalization over its rules and its fuel, the reduction over
its rules, its fuel and its depth, the application of a theorem over its index and objects, the
evaluation at literals over its index, and the reduction by the machine over its fuel, the bound
and the exceptions of the definitions it unfolds, the indices of the primitives of lists and its
rules. -/
def convData : ConvRule → ℕ × List Tree
  | .base r => ruleData r
  | .norm rs fuel => (37, [RoseTree.node 0 (rs.map encRule), leaf fuel])
  | .eval rs fuel depth =>
    (38, [RoseTree.node 0 (rs.map encRule), leaf fuel, leaf (encDepth depth)])
  | .applyMatch j θ => (39, [leaf j, RoseTree.node 0 θ])
  | .lit j => (40, [leaf j])
  | .machine fuel m except kl kc rs =>
    (41, [leaf fuel, leaf m, RoseTree.node 0 (except.map leaf), leaf kl, leaf kc,
      RoseTree.node 0 (rs.map encRule)])

/-- A certificate as the node of its rule's position over the node of the rule's data and its
premises. -/
def encConv : ConvDeriv → Tree :=
  encWith (fun l ↦ (convData l).1) fun l ↦ RoseTree.node 0 (convData l).2

/-- The encoding of a certificate's node. -/
theorem encConv_node (l : ConvRule) (cs : List ConvDeriv) :
    encConv (RoseTree.node l cs) =
      RoseTree.node (convData l).1 (RoseTree.node 0 (convData l).2 :: cs.map encConv) :=
  encWith_node _ _ l cs

/-- A reduction's certificate with its mark, as the node of the two. -/
def encCB (p : ConvDeriv × Bool) : Tree := encPair (encConv p.1, ofBool p.2)

/-- A term with its reduction's certificate and mark. -/
def encTCB (p : Term × ConvDeriv × Bool) : Tree := encPair (encTerm p.1, encCB p.2)

/-- The certificate of an encoded reduction's rewriting. -/
@[simp] theorem p1_encCB (p : ConvDeriv × Bool) : «Language.p1» (encCB p) = encConv p.1 :=
  rfl

/-- The mark of an encoded reduction's rewriting. -/
@[simp] theorem p2_encCB (p : ConvDeriv × Bool) : «Language.p2» (encCB p) = ofBool p.2 :=
  rfl

/-- The term of an encoded reduction. -/
@[simp] theorem p1_encTCB (p : Term × ConvDeriv × Bool) :
    «Language.p1» (encTCB p) = encTerm p.1 :=
  rfl

/-- The rewriting of an encoded reduction. -/
@[simp] theorem p2_encTCB (p : Term × ConvDeriv × Bool) :
    «Language.p2» (encTCB p) = encCB p.2 :=
  rfl

/-- A term with a certificate. -/
def encTC (p : Term × ConvDeriv) : Tree := encPair (encTerm p.1, encConv p.2)

/-- The term of an encoded pair of a term and a certificate. -/
@[simp] theorem p1_encTC (p : Term × ConvDeriv) : «Language.p1» (encTC p) = encTerm p.1 :=
  rfl

/-- The certificate of an encoded pair of a term and a certificate. -/
@[simp] theorem p2_encTC (p : Term × ConvDeriv) : «Language.p2» (encTC p) = encConv p.2 :=
  rfl

/-- The mirror's derivation of a rule's position and data over encoded certificates, as the
certificate of the rule of the language. -/
theorem dNode_conv (r : Internal.Rule) (cs : List ConvDeriv) :
    «Prover.dNode» (leaf (ruleData r).1) (ruleData r).2 (cs.map encConv) =
      encConv (RoseTree.node (.base r) cs) := by
  simp [«Prover.dNode», «Language.mNode», encConv_node, convData]

/-! The reductions that name steps. -/

/-- The mirror's rule that a step names for a rule related to a rule of the normalizer: the
encoding of the rule before its preparation. -/
theorem ruleNode_eq (r' : Tree) (r : NormRule) (h : RRel r' r) :
    «Prover.ruleNode» r' = encRule r.unprepare := by
  cases r
  case thmAt j θ root m k =>
    obtain ⟨p, -, h1, -⟩ := h
    simp only [«Prover.ruleNode», template, h1]
    mirror_simp [List.getD_cons_zero, List.getD_cons_succ, Internal.NormRule.unprepare, encRule]
    rfl
  all_goals
    simp only [RRel] at h
    simp only [«Prover.ruleNode», template, h, encRule]
    mirror_simp [Internal.NormRule.unprepare, encRule]

/-- The mirror's node of the rules a step names, for rules related to the normalizer's. -/
theorem rulesNode_eq (rs' : List Tree) (rs : List NormRule) (h : List.Forall₂ RRel rs' rs) :
    «Prover.rulesNode» rs' = RoseTree.node 0 ((rs.map NormRule.unprepare).map encRule) := by
  have hm : rs'.map «Prover.ruleNode» = (rs.map NormRule.unprepare).map encRule := by
    revert rs
    exact rs'.rec (fun rs h ↦ by cases h; rfl) fun r' rs' ih rs h ↦ by
      cases h with
      | cons hr h' => simp only [List.map_cons, ruleNode_eq _ _ hr, ih _ h']
  simp only [«Prover.rulesNode», template, mapT_eq, hm, node_leaf]

/-- A derivation as a certificate is encoded as the derivation is. -/
theorem encConv_liftDeriv (d : Deriv) : encConv (Internal.liftDeriv d) = encDeriv d :=
  RoseTree.ind (P := fun d ↦ encConv (Internal.liftDeriv d) = encDeriv d) (fun r cs ih ↦ by
    rw [Internal.liftDeriv, RoseTree.map_node, encConv_node, encDeriv_node, List.map_map]
    exact congrArg (fun xs ↦ RoseTree.node (ruleData r).1 (RoseTree.node 0 (ruleData r).2 :: xs))
      (List.map_congr_left fun c hc ↦ ih c hc)) d

/-- The mirror's number of an encoded derivation's nodes. -/
theorem dSize_eq (d : Deriv) : «Prover.dSize» (encDeriv d) = leaf (Internal.derivSize d) := by
  have hp : ∀ d : Deriv, RoseTree.para (fun (_ : Internal.Rule) (cs : List (Deriv × ℕ)) ↦
      1 + (cs.map Prod.snd).sum) d = Internal.derivSize d :=
    RoseTree.ind fun r cs ih ↦ by
      rw [RoseTree.para_node, Internal.derivSize, RoseTree.elim_node, List.map_map]
      exact congrArg (fun xs ↦ 1 + List.sum xs) (List.map_congr_left fun c hc ↦ ih c hc)
  rw [← hp d]
  simp only [«Prover.dSize», template]
  refine para_enc _ _ (fun (v : Tree) (w : ℕ) ↦ v = leaf w) _ _ (fun l v xs hx ↦ ?_) d
  have hs : ∀ ys : List (Deriv × Tree × ℕ), (∀ x ∈ ys, x.2.1 = leaf x.2.2) →
      List.foldr (fun x acc ↦ Const.add x acc) (leaf 0) (ys.map fun x ↦ x.2.1) =
        leaf ((ys.map fun x ↦ x.2.2).sum) :=
    List.rec (fun _ ↦ rfl) fun y ys ih h ↦ by
      simp only [List.map_cons, List.foldr_cons, List.sum_cons]
      rw [ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx), h y List.mem_cons_self]
      rfl
  mirror_simp [List.tail_cons, List.map_map, Function.comp_def]
  rw [hs xs hx]
  rfl

/-- The mirror's bound on the nodes of a derivation a prover keeps. -/
theorem stepBound_eq : «Prover.stepBound» = leaf Internal.stepBound := rfl

/-- The mirror's result of a reduction with the certificate of its rewriting, at an encoded
step. -/
theorem stepped_eq (c : ConvDeriv) (x : Term × Deriv × Bool) :
    «Prover.stepped» (encConv c) (encTDB x) = encTCB (Internal.stepped (fun _ ↦ c) x) := by
  rcases x with ⟨t, d, _ | _⟩
  · rfl
  · simp only [«Prover.stepped», template, p1_encTDB, p2_encTDB, p1_encDB, p2_encDB, dSize_eq,
      stepBound_eq, lt_leaf, Internal.stepped]
    by_cases h : Internal.stepBound < Internal.derivSize d
    · simp [h, encTCB, encCB, ofBool]
    · simp [h, encTCB, encCB, encDB, ofBool, encConv_liftDeriv]

/-- The mirror's normalization and a normalization that names its step are related when they
agree at every context, encoded hypotheses and encoded term. -/
def NRelC (v : List Tree → List Tree → Tree → Tree)
    (w : List Tree → List Term → Term → Option (Term × ConvDeriv × Bool)) : Prop :=
  ∀ Γ Φ t, v Γ (Φ.map encTerm) (encTerm t) = encOpt ((w Γ Φ t).map encTCB)

/-- The mirror's reduction and a reduction that names its step are related when they agree at
every depth, context, encoded hypotheses and encoded term. -/
def ERelC (v : Tree → List Tree → List Tree → Tree → Tree)
    (w : Internal.Depth → List Tree → List Term → Term → Option (Term × ConvDeriv × Bool)) :
    Prop :=
  ∀ dp Γ Φ t, v (leaf (encDepth dp)) Γ (Φ.map encTerm) (encTerm t) =
    encOpt ((w dp Γ Φ t).map encTCB)

variable (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ)

/-- The mirror's normalization innermost first that names its step, at related rules. -/
theorem normalizeC_eq (rs' : List Tree) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) :
    NRelC («Prover.normalize» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (leaf fuel))
      (Internal.normalizeC G E n rs fuel) := by
  intro Γ Φ t
  have hs : «Prover.dNode» (leaf 37) [«Prover.rulesNode» rs', leaf fuel] [] =
      encConv (RoseTree.node (.norm (rs.map NormRule.unprepare) fuel) []) := by
    simp [«Prover.dNode», «Language.mNode», encConv_node, convData, rulesNode_eq rs' rs hrs]
  simp only [«Prover.normalize», template, «Theory.l2», single_eq, hs,
    normalizeD_eq G E n rs' rs hrs fuel Γ Φ t, mapO_eq, Option.map_map, Internal.normalizeC,
    Function.comp_def, stepped_eq]

/-- The mirror's reduction to a depth that names its step, at related rules. -/
theorem evalC_eq (rs' : List Tree) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) :
    ERelC («Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (leaf fuel))
      (Internal.evalC G E n rs fuel) := by
  intro dp Γ Φ t
  have hs : «Prover.dNode» (leaf 38)
      [«Prover.rulesNode» rs', leaf fuel, leaf (encDepth dp)] [] =
      encConv (RoseTree.node (.eval (rs.map NormRule.unprepare) fuel dp) []) := by
    simp [«Prover.dNode», «Language.mNode», encConv_node, convData, rulesNode_eq rs' rs hrs]
  simp only [«Prover.eval», template, «Theory.l3», «Theory.l2», single_eq, hs,
    evalD_eq G E n rs' rs hrs fuel dp Γ Φ t, mapO_eq, Option.map_map, Internal.evalC,
    Function.comp_def, stepped_eq]

/-- The mirror's normal form reached through weak head normal forms, at related rules. -/
theorem normalizeWC_eq (rs' : List Tree)
    (rs : List NormRule) (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) :
    NRelC («Prover.normalizeW» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (leaf fuel))
      (Internal.normalizeWC G E n rs fuel) :=
  evalC_eq G E n rs' rs hrs fuel .full

/-- The mirror's proof of an equation by reducing both sides, by related reductions, to one
term. -/
theorem joinBy_eq (v : List Tree → List Tree → Tree → Tree)
    (w : List Tree → List Term → Term → Option (Term × ConvDeriv × Bool)) (h : NRelC v w)
    (Γ : List Tree) (Φ : List Term) (t u : Term) :
    «Prover.joinBy» v Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((do
        let (v₁, d₁, _) ← w Γ Φ t
        let (v₂, d₂, _) ← w Γ Φ u
        if v₁ = v₂ then some (RoseTree.node (ConvRule.base .join) [d₁, d₂]) else none).map
          encConv) := by
  simp only [«Prover.joinBy», template, h Γ Φ t, h Γ Φ u, bindO_eq]
  rcases w Γ Φ t with _ | ⟨v₁, d₁, b₁⟩
  · rfl
  rcases w Γ Φ u with _ | ⟨v₂, d₂, b₂⟩
  · rfl
  have hj := dNode_conv .join [d₁, d₂]
  simp only [ruleData, List.map_cons, List.map_nil] at hj
  by_cases hv : v₁ = v₂ <;>
    simp [hv, encTCB, encCB, p1_eq, p2_eq, encTerm_eq_iff, hj, «Theory.l2»,
      none_eq, some_eq]

/-- The mirror's proof of an equation by normalizing both sides to one term. -/
theorem byNorm_eq (rs' : List Tree) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t u : Term) :
    «Prover.byNorm» (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf fuel) Γ
        (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byNorm G E n rs fuel Γ Φ t u).map encConv) := by
  rw [«Prover.byNorm», joinBy_eq _ _ (normalizeC_eq G E n rs' rs hrs fuel)]
  rfl

/-! Induction. -/

/-- The simplification of a case of the mirror's induction: the options, lists and pairs of the
program, the checker's instances, and the given lemmas, the maps of encodings left unfused so
that the proofs by normalization apply. -/
local macro "ind_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [bindO_eq, mapO_eq, children_eq, RoseTree.children_node, lcase_cons, lcase_nil,
    lowerHyps_eq, natSuccAt_eq, listConsAt_eq, weakenElem_eq, instAt_eq, subst_atVar0, mEq_eq,
    single_eq, length_eq, mapT_weaken2, mapT_weaken1, snocHyp_eq, p1_encTCB, p2_encTCB,
    p1_encCB, p2_encCB, Option.bind_eq_bind, Option.pure_def, Option.map_bind, Option.bind_map,
    Option.map_map, Option.elim_some, Option.elim_none, Option.map_some, Option.map_none,
    Option.bind_some, Option.bind_none, Function.comp_def, none_eq, some_eq, elim_encOpt,
    «Theory.l3», «Theory.l2», encConv_node, convData, ruleData,
    «Prover.dNode», «Language.mNode», node_leaf, List.map_cons, List.map_nil,
    $ls,*])

/-- The mirror's proof of an equation by induction on a natural number variable with a step,
each premise by normalization. -/
theorem byNatInd_eq (kz ks : ℕ) (s : Term) (rs' : List Tree)
    (rs : List NormRule) (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) :
    «Prover.byNatInd» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kz)
        (leaf ks) (encTerm s) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byNatInd G E n kz ks s rs fuel Γ Φ t u).map encConv) := by
  rcases Γ with _ | ⟨c, Γ'⟩
  · rfl
  simp only [«Prover.byNatInd», template, Internal.byNatInd]
  ind_simp [byNorm_eq G E n rs' rs hrs]
  rcases Internal.lowerHyps G n Γ' Φ with _ | Φ'
  · rfl
  ind_simp [byNorm_eq G E n rs' rs hrs]
  simp only [Option.map_eq_bind, Function.comp_def]

/-- The mirror's proof of an equation by induction on a list variable with a step, each premise
by normalization. -/
theorem byListInd_eq (kn kc : ℕ) (s : Term) (rs' : List Tree)
    (rs : List NormRule) (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) :
    «Prover.byListInd» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn)
        (leaf kc) (encTerm s) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byListInd G E n kn kc s rs fuel Γ Φ t u).map encConv) := by
  rcases Γ with _ | ⟨c, Γ'⟩
  · rfl
  simp only [«Prover.byListInd», template, Internal.byListInd, listPart_eq]
  ind_simp []
  rcases Internal.listPart c with _ | a
  · rfl
  ind_simp [byNorm_eq G E n rs' rs hrs]
  rcases Internal.lowerHyps G n Γ' Φ with _ | Φ'
  · rfl
  ind_simp [byNorm_eq G E n rs' rs hrs]
  simp only [Option.map_eq_bind, Function.comp_def]

/-- The mirror's proof of an equation by induction on a natural number variable with the
induction hypothesis. -/
theorem byNatIndHyp_eq (kz ks : ℕ) (rs' : List Tree)
    (rs : List NormRule) (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) :
    «Prover.byNatIndHyp» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kz)
        (leaf ks) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byNatIndHyp G E n kz ks rs fuel Γ Φ t u).map encConv) := by
  rcases Γ with _ | ⟨c, Γ'⟩
  · rfl
  have hN : ∀ Γ Φ t, «Prover.normalize» (encGlobals G) (E.toList.map encEntry)
      (leaf n) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.normalizeC G E n rs fuel Γ Φ t).map encTCB) :=
    normalizeC_eq G E n rs' rs hrs fuel
  have hW := byNorm_eq G E n _ _ (withHyp_eq rs' rs hrs (Φ.length + 1)) fuel
  simp only [«Prover.byNatIndHyp», template, Internal.byNatIndHyp]
  ind_simp [byNorm_eq G E n rs' rs hrs]
  rcases Internal.lowerHyps G n Γ' Φ with _ | Φ'
  · rfl
  ind_simp [byNorm_eq G E n rs' rs hrs, hN, List.length_map, List.length_append,
    List.length_singleton, hW]
  rcases Internal.byNorm G E n rs fuel Γ' Φ'
    (t.subst (Internal.instVar (Term.arr kz [] Term.star)))
    (u.subst (Internal.instVar (Term.arr kz [] Term.star))) with _ | p₀
  · rfl
  ind_simp [hN, hW, List.length_map, List.length_append, List.length_singleton]
  rcases Internal.normalizeC G E n rs fuel (c :: Γ') (Φ ++ [t.eq u]) (t.eq u) with _ | ⟨ψ, dψ, b⟩
  · rfl
  ind_simp [hN, hW, List.length_map, List.length_append, List.length_singleton]

/-- The mirror's proof of an equation by induction on a list variable with the induction
hypothesis. -/
theorem byListIndHyp_eq (kn kc : ℕ) (rs' : List Tree)
    (rs : List NormRule) (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) :
    «Prover.byListIndHyp» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn)
        (leaf kc) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byListIndHyp G E n kn kc rs fuel Γ Φ t u).map encConv) := by
  rcases Γ with _ | ⟨c, Γ'⟩
  · rfl
  have hN : ∀ Γ Φ t, «Prover.normalize» (encGlobals G) (E.toList.map encEntry)
      (leaf n) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.normalizeC G E n rs fuel Γ Φ t).map encTCB) :=
    normalizeC_eq G E n rs' rs hrs fuel
  simp only [«Prover.byListIndHyp», template, Internal.byListIndHyp, listPart_eq]
  ind_simp []
  rcases Internal.listPart c with _ | a
  · rfl
  ind_simp [byNorm_eq G E n rs' rs hrs]
  rcases Internal.lowerHyps G n Γ' Φ with _ | Φ'
  · rfl
  have hW := byNorm_eq G E n _ _ (withHyp_eq rs' rs hrs (Φ'.length + 1)) fuel
  ind_simp [byNorm_eq G E n rs' rs hrs]
  rcases Internal.byNorm G E n rs fuel Γ' Φ'
    (t.subst (Internal.instVar (Term.arr kn [a] Term.star)))
    (u.subst (Internal.instVar (Term.arr kn [a] Term.star))) with _ | p₀
  · rfl
  ind_simp [hN, hW, List.length_map, List.length_append, List.length_singleton]
  rcases Internal.normalizeC G E n rs fuel (c :: a :: Γ')
    (Φ'.map Internal.weaken2 ++ [Internal.weakenElem (t.eq u)]) (Internal.weakenElem (t.eq u))
    with _ | ⟨ψ, dψ, b⟩
  · rfl
  ind_simp [hN, hW, List.length_map, List.length_append, List.length_singleton]

/-- The mirror's proof of an equation by normalizing both sides, weak head normal forms first,
to one term. -/
theorem byNormW_eq (rs' : List Tree) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t u : Term) :
    «Prover.byNormW» (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf fuel)
        Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byNormW G E n rs fuel Γ Φ t u).map encConv) := by
  rw [«Prover.byNormW», joinBy_eq _ _ (normalizeWC_eq G E n rs' rs hrs fuel)]
  rfl

/-! Provers of equations. -/

/-- The mirror's prover and a prover are related when they agree at every context, encoded
hypotheses and encoded sides. -/
def PRel (v : List Tree → List Tree → Tree → Tree → Tree) (w : Internal.Prover) : Prop :=
  ∀ Γ Φ t u, v Γ (Φ.map encTerm) (encTerm t) (encTerm u) = encOpt ((w Γ Φ t u).map encConv)

/-- The mirror's abstraction of an encoded term over a variable. -/
@[simp] theorem abstractVar_eq (i : ℕ) (c : Tree) (t : Term) :
    «Prover.abstractVar» (leaf i) c (encTerm t) =
      encTerm (Internal.abstractVar i c t) := by
  simp only [«Prover.abstractVar», template, weaken1_eq, Internal.abstractVar]
  rw [subst_eq _ _ (fun j ↦ if j = i + 1 then Term.var 0 else Term.var j) fun j ↦ by
    mirror_simp [beq_iff_eq]
    split <;> rfl, mLam_eq]

/-- The mirror's proof of an equation of functions by extensionality, at a related prover. -/
theorem byFunExt_eq (p' : List Tree → List Tree → Tree → Tree → Tree) (p : Internal.Prover)
    (hp : PRel p' p) :
    PRel («Prover.byFunExt» (encGlobals G) (leaf n) p') (Internal.byFunExt G n p) := by
  have hp' : ∀ Γ Φ t u, p' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p Γ Φ t u).map encConv) := hp
  intro Γ Φ f g
  simp only [«Prover.byFunExt», template, Internal.byFunExt, typeIn_eq]
  ind_simp [expParts_eq]
  rcases Internal.typeIn G n Γ f with _ | c
  · rfl
  ind_simp [expParts_eq]
  rcases Internal.expParts c with _ | ⟨a, b⟩
  · rfl
  ind_simp [p1_eq, weaken1_eq, mApp_eq, mVar_eq, hp']
  simp only [Option.map_eq_bind, Function.comp_def]

/-- The mirror's proof of an equation by case analysis on a variable of a coproduct, at a
related prover. -/
theorem bySplit_eq (kl kr i : ℕ) (p' : List Tree → List Tree → Tree → Tree → Tree)
    (p : Internal.Prover) (hp : PRel p' p) :
    PRel («Prover.bySplit» (leaf kl) (leaf kr) (leaf i) p')
      (Internal.bySplit kl kr i p) := by
  have hp' : ∀ Γ Φ t u, p' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p Γ Φ t u).map encConv) := hp
  intro Γ Φ t u
  simp only [«Prover.bySplit», template, Internal.bySplit]
  ind_simp [nth_eq]
  rcases Γ[i]? with _ | c
  · rfl
  ind_simp [coprodParts_eq]
  rcases Internal.coprodParts c with _ | ⟨a, b⟩
  · rfl
  ind_simp [p1_eq, p2_eq, abstractVar_eq, weaken1_eq, mApp_eq, mArr_eq, mVar_eq, hp',
    List.length_map]
  rfl

/-- The mirror's proof of an equation by induction on a list variable with the induction
hypothesis, each premise by its related prover. -/
theorem byListIndWith_eq (kn kc : ℕ) (p₀' p₁' : List Tree → List Tree → Tree → Tree → Tree)
    (p₀ p₁ : Internal.Prover) (hp₀ : PRel p₀' p₀) (hp₁ : PRel p₁' p₁) :
    PRel («Prover.byListIndWith» (encGlobals G) (leaf n) (leaf kn) (leaf kc) p₀' p₁')
      (Internal.byListIndWith G n kn kc p₀ p₁) := by
  have hp₀' : ∀ Γ Φ t u, p₀' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p₀ Γ Φ t u).map encConv) := hp₀
  have hp₁' : ∀ Γ Φ t u, p₁' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p₁ Γ Φ t u).map encConv) := hp₁
  intro Γ Φ t u
  rcases Γ with _ | ⟨c, Γ'⟩
  · rfl
  simp only [«Prover.byListIndWith», template, Internal.byListIndWith, listPart_eq]
  ind_simp []
  rcases Internal.listPart c with _ | a
  · rfl
  ind_simp []
  rcases Internal.lowerHyps G n Γ' Φ with _ | Φ'
  · rfl
  ind_simp [hp₀', hp₁']
  simp only [Option.map_eq_bind, Function.comp_def]

/-- The mirror's proof of an equation in a context of a rose tree alone by the uniqueness of the
fold, each premise by normalization. -/
theorem byRoseInd_eq (kn kl kc : ℕ) (s : Term)
    (rs' : List Tree) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree) (t u : Term) :
    «Prover.byRoseInd» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn)
        (leaf kl) (leaf kc) (encTerm s) rs' (leaf fuel) Γ (encTerm t) (encTerm u) =
      encOpt ((Internal.byRoseInd G E n kn kl kc s rs fuel Γ t u).map encConv) := by
  have hB : ∀ Γ t u, «Prover.byNorm» (encGlobals G) (E.toList.map encEntry) (leaf n)
      rs' (leaf fuel) Γ [] (encTerm t) (encTerm u) =
      encOpt ((Internal.byNorm G E n rs fuel Γ [] t u).map encConv) :=
    fun Γ t u ↦ byNorm_eq G E n rs' rs hrs fuel Γ [] t u
  rcases Γ with _ | ⟨r, _ | ⟨r', Γ'⟩⟩ <;>
    simp only [«Prover.byRoseInd», template, Internal.byRoseInd]
  · rfl
  · mirror_simp [roseLabel_eq, typeIn_eq, Theory.mirror_list, «Theory.l4»,
      «Theory.l2», Option.bind_eq_bind]
    rcases Internal.roseParts r with _ | ⟨a, f⟩
    · rfl
    rcases Internal.typeIn G n [r] t with _ | C
    · rfl
    ind_simp [roseNodeAt_eq, roseMapAt_eq, hB]
    simp only [Option.map_eq_bind, Function.comp_def]
  · mirror_simp [beq_iff_eq, Nat.reduceEqDiff, none_eq]

/-- The mirror's proof of an equation in a context of a rose tree alone by induction with the
hypothesis at each child, at a related prover. -/
theorem byRoseIndHyp_eq (kn kl kc : ℕ) (p' : List Tree → List Tree → Tree → Tree → Tree)
    (p : Internal.Prover) (hp : PRel p' p) :
    PRel («Prover.byRoseIndHyp» (leaf kn) (leaf kl) (leaf kc) p')
      (Internal.byRoseIndHyp kn kl kc p) := by
  have hp' : ∀ Γ Φ t u, p' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p Γ Φ t u).map encConv) := hp
  intro Γ Φ t u
  rcases Γ with _ | ⟨r, Γ'⟩ <;> rcases Φ with _ | ⟨φ, Φ⟩ <;>
    simp only [«Prover.byRoseIndHyp», template, Internal.byRoseIndHyp]
  · mirror_simp [none_eq, List.isEmpty_nil, Bool.not_true, Bool.false_and]
  · mirror_simp [none_eq, List.isEmpty_nil, Bool.not_true, Bool.false_and]
  · mirror_simp [roseLabel_eq, Theory.mirror_list, «Theory.l3», Option.bind_eq_bind,
      List.isEmpty_nil, List.isEmpty_cons, Bool.not_false, Bool.true_and, List.getD_cons_zero,
      List.tail_cons]
    rcases Internal.roseParts r with _ | ⟨a, f⟩
    · rfl
    have h := hp' (list r :: a :: Γ') [Internal.roseHyp kl kc (Term.eq t u)]
      (Internal.roseNodeAt kn r a t) (Internal.roseNodeAt kn r a u)
    simp only [List.map_cons, List.map_nil] at h
    ind_simp [roseNodeAt_eq, roseHyp_eq, mEq_eq, h]
    simp only [Option.map_eq_bind, Function.comp_def]
  · mirror_simp [none_eq, List.isEmpty_cons, Bool.and_false]

end GebTests.Prototypes.FreeTopos.Agreement.Provers

end
