/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Literals
public import GebTests.Prototypes.FreeTopos.Agreement.Machine
public import GebTests.Prototypes.FreeTopos.Agreement.Prove
public import Geb.Prototypes.FreeTopos.Internal.Conversion
public import Geb.Prototypes.FreeTopos.Internal.Accelerate

set_option doc.verso true in
/-!
# The conversion checker written in Geb

The functions of {lit}`bootstrap/free-topos/conversion.geb`, in the Lean the bootstrap compiler
emits ({lit}`GebMirror.Metalogic`), agree with the checker of the internal language with a step
of conversion ({name}`Geb.FreeTopos.Internal.convCheck`) at every encoded certificate whose rules
the mirror reads: the rule of the language a certificate's root stands for, the rules of the
normalizer a step names, the instance of a theorem whose conclusion matches a formula, the
reduction by the environment machine with its rewriting by the prover's rules, the step of the
checker at a node and the checker, so that the two checkers accept the same certificates of the
same theorems.

A certificate is encoded as a derivation is, the node of its rule's position over the node of the
rule's data and its premises: a rule of the language at its position and with its data, and the
steps of conversion and the application of a theorem at the positions after the language's rules.
A rule of the normalizer that holds a prepared theorem holds a matching, a function, which no
tree encodes, so that the agreement is stated at the certificates none of whose steps names one;
a step of the prover's reductions, and a step of the machine, names its rules before they are
prepared. A declaration of a development is the node of its constructor's position over its
fields, a declaration of the base checker as that checker's agreement encodes it, and the state
of the check the node of the constants, the node of the entries and the node of the indices at
which the evaluation at literals is ready.

## Main definitions

* {lit}`convData`, {lit}`encConv` — the encoding of a rule of the certificates and of a
  certificate.
* {lit}`RulePlain`, {lit}`Plain` — the rules of the certificates the mirror reads, and the
  certificates of such rules.
* {lit}`encConvDecl`, {lit}`encConvState`, {lit}`DeclPlain` — the encoding of a declaration of a
  development with certificates and of the state of its check, and the declarations the mirror
  reads.

## Main statements

* {lit}`toRule_eq` — the mirror's rule of the language a certificate's root stands for.
* {lit}`applyInst_eq` — the mirror's instance of a theorem whose conclusion matches a formula.
* {lit}`machineReduceBy_eq` — the mirror's reduction of a term by the machine, rewriting its
  normal form by the prover's rules.
* {lit}`convStep_eq` — the mirror's step of the checker.
* {lit}`convCheck_eq` — the mirror's checker.
* {lit}`thmConvChecks_eq` — the mirror's test that a certificate proves a theorem.
* {lit}`convDeclStep_eq`, {lit}`checkConvDev_eq` — the mirror's check of a declaration, and of
  a development's declarations in order.

## Tags

proof checker, conversion, internal language, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Conversion

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Fold GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.Language
  GebTests.Prototypes.FreeTopos.Agreement.Derivation
  GebTests.Prototypes.FreeTopos.Agreement.Prove
open Internal (Term Deriv NormRule ConvRule ConvDeriv)
open scoped FinEnum

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

/-- Rules of the normalizer none of which is a prepared theorem, whose matching no tree
encodes. -/
def Unprepared (rs : List NormRule) : Prop := ∀ r ∈ rs, ∀ j θ root m k, r ≠ .thmAt j θ root m k

/-- A rule of the certificates the mirror reads: a step of the prover's reductions, and a step
of the machine, names no prepared theorem. -/
def RulePlain : ConvRule → Prop
  | .norm rs _ | .eval rs _ _ | .machine _ _ _ _ _ rs => Unprepared rs
  | _ => True

/-- A certificate each of whose rules the mirror reads. -/
def Plain : ConvDeriv → Prop := RoseTree.elim fun l cs ↦ RulePlain l ∧ ∀ c ∈ cs, c

/-- A node is a certificate the mirror reads exactly when its rule is one and its premises
are. -/
theorem plain_node {l : ConvRule} {cs : List ConvDeriv} :
    Plain (RoseTree.node l cs) ↔ RulePlain l ∧ ∀ c ∈ cs, Plain c := by
  unfold Plain
  rw [RoseTree.elim_node]
  exact and_congr_right fun _ ↦ ⟨fun h c hc ↦ h _ (List.mem_map_of_mem hc), fun h p hp ↦ by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact h c hc⟩

/-- The position of a rule of the language is below the positions of the certificates' other
rules. -/
theorem ruleData_lt (r : Internal.Rule) : (ruleData r).1 < 37 := by
  cases r <;> simp [ruleData]

/-! The rules a certificate names. -/

/-- The mirror's rule of the normalizer read from an encoded rule is that encoding. -/
theorem ruleOf_eq (r : NormRule) : «Conversion.ruleOf» (encRule r) = encRule r := by
  cases r <;> simp [«Conversion.ruleOf», encRule, template] <;> rfl

/-- The mirror's rules of the normalizer read from encoded rules are those encodings. -/
theorem rulesOf_eq (rs : List NormRule) :
    «Conversion.rulesOf» (rs.map encRule) = rs.map encRule := by
  simp only [«Conversion.rulesOf», «$436f6e76657273696f6e2f52756c6541742e6d6170», foldr_eq]
  exact List.rec rfl (fun r rs ih ↦ by
    simp only [List.map_cons, List.foldr_cons, ih, ruleOf_eq]) rs

/-- Encoded rules none of which is a prepared theorem are related to the rules. -/
theorem forall₂_rrel {rs : List NormRule} (h : Unprepared rs) :
    List.Forall₂ RRel (rs.map encRule) rs := by
  rw [List.forall₂_map_left_iff]
  refine List.forall₂_same.mpr fun r hr ↦ ?_
  cases r
  case thmAt j θ root m k => exact absurd rfl (h _ hr j θ root m k)
  all_goals rfl

/-- The mirror's rule of the language an encoded certificate's root stands for, as a derivation
without premises. -/
theorem toRule_eq (c : ConvDeriv) :
    «Conversion.toRule» (encConv c) = encDeriv (RoseTree.node c.label.toRule []) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, c = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children c).symm⟩
  rw [encConv_node, RoseTree.label_node]
  cases l with
  | base r =>
    have h := ruleData_lt r
    simp [«Conversion.toRule», convData, ConvRule.toRule, encDeriv, h]
  | applyMatch j θ =>
    simp [«Conversion.toRule», convData, ConvRule.toRule, encDeriv, ruleData,
      «Language.mD», «Language.mData», «Theory.l3», «Theory.l2»]
  | _ => simp [«Conversion.toRule», convData, ConvRule.toRule, encDeriv, ruleData]

/-- The mirror's derivation of a rule of the language with its data over the rules an encoded
certificate's premises stand for. -/
theorem baseNode_eq (r : Internal.Rule) (l : ConvRule) (cs : List ConvDeriv) :
    «Conversion.baseNode» (leaf (ruleData r).1) (RoseTree.node 0 (ruleData r).2)
        (encConv (RoseTree.node l cs)) =
      encDeriv (RoseTree.node r (cs.map fun c ↦ RoseTree.node c.label.toRule [])) := by
  simp only [«Conversion.baseNode», encConv_node, children_eq, RoseTree.children_node, tail_eq,
    List.tail_cons, mapT_eq, List.map_map, node_leaf, encDeriv, encWith_node]
  exact congrArg _ (congrArg _ (List.map_congr_left fun c _ ↦ toRule_eq c))

/-! The application of a theorem. -/

variable (G : Internal.Globals) (E : Array Internal.Entry) (R : List ℕ) (n : ℕ)

/-- A case analysis of an optional tree, as the compiler emits it, is the base's binding. -/
theorem case_bindO (m : Tree) (f : Tree → Tree) :
    (if (Const.eq (Const.label m) (leaf 1)).label ≠ 0 then f (Const.child m (leaf 0))
      else «Prelude.none») = «Base.bindO» m f := rfl

/-- The mirror's instance of a theorem whose conclusion matches an encoded formula. -/
theorem applyInst_eq (j : ℕ) (θ : List Tree) (φ : Term) :
    «Conversion.applyInst» (E.toList.map encEntry) (leaf j) θ (encTerm φ) =
      encOpt ((Internal.applyInst E j θ φ).map fun σ ↦ RoseTree.node 0 (σ.map encTerm)) := by
  have hr : ∀ k : ℕ, «Prelude.replicate» (leaf k) «Prelude.none» =
      (List.replicate k (none : Option Term)).map encOT := fun k ↦ by
    rw [replicate_eq, List.map_replicate]
    rfl
  simp only [«Conversion.applyInst», template, Internal.applyInst, nth_eq, List.getElem?_map,
    Array.getElem?_toList]
  rcases E[j]? with _ | (a | s)
  · mirror_simp [none_eq]
    rfl
  · have hp : (if θ.isEmpty = true then encTerm a.concl
        else «Language.osubst» θ (encTerm a.concl)) =
        encTerm (if θ.isEmpty then a.concl else Term.osubst θ a.concl) := by
      split <;> simp [osubst_eq]
    have hrep : List.replicate a.ctx.length (encOpt none) =
        (List.replicate a.ctx.length (none : Option Term)).map encOT := by
      rw [List.map_replicate]
      rfl
    mirror_simp [entryLanguage_eq, Internal.Entry.language?, thConcl_eq, thCtx_eq, some_eq,
      none_eq, isEmpty_eq, length_eq, hr]
    rw [hp, hrep, matchTerm_eq _ 0 φ]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rcases Internal.matchTerm _ 0 φ _ with _ | σ
    · rfl
    · have hs : RoseTree.children (encSigma σ) = σ.map fun o ↦ encOpt (o.map encTerm) := by
        simp [encSigma, encOT]
      simp only [Option.map_some, encOpt_some_label, beq_self_eq_true, ↓reduceIte,
        child_encOpt_some, hs, allSomeT_eq, Option.bind_some,
        Infer.mapM_map_option (fun o : Option Term ↦ o) encTerm, Option.map_map]
      rfl
  · mirror_simp [entryLanguage_eq, Internal.Entry.language?, none_eq]
    rfl

/-! The reduction by the machine. -/

/-- The rewriting at the root by prepared rules is the rewriting by the rules. -/
theorem rootRewrite_prepareRules (rs : List NormRule) (Γ : List Tree) (Φ : List Term)
    (t : Term) :
    Internal.rootRewrite G E n (Internal.prepareRules E rs) Γ Φ t =
      Internal.rootRewrite G E n rs Γ Φ t := by
  simp only [Internal.rootRewrite, Internal.prepareRules, List.findSome?_map]
  exact congrArg (List.findSome? · rs)
    (funext fun r ↦ Internal.tryRule_prepareRule G E n Γ Φ t r)

/-- The mirror's reduction of an encoded term in a context under encoded hypotheses by the
machine, at a predicate related to the machine's and at encoded rules none of which is a prepared
theorem. -/
theorem machineReduceBy_eq (unf' : Tree → Tree) (unfold : ℕ → Bool)
    (hunf : ∀ j, unf' (leaf j) = ofBool (unfold j)) (kl kc : ℕ) (rs : List NormRule)
    (hrs : Unprepared rs) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t : Term) :
    «Conversion.machineReduceBy» (encGlobals G) (E.toList.map encEntry) (leaf n) unf' (leaf kl)
        (leaf kc) (rs.map encRule) (leaf fuel) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.machineReduceBy G E n unfold kl kc rs fuel Γ Φ t).map encTerm) := by
  have hemp : «$436f6e76657273696f6e2f4561636852756c652e6973456d707479»
      (rs.map encRule) = ofBool rs.isEmpty := by
    simp only [template, isEmpty_eq, List.isEmpty_map]
  simp only [«Conversion.machineReduceBy», hemp, ofBool_bne, label_ne_zero,
    Internal.machineReduceBy]
  cases hr : rs.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact Machine.machineReduce_eq (P := ⟨encGlobals G, leaf n, unf', leaf kl, leaf kc, _⟩)
      ⟨rfl, rfl, hunf, rfl, rfl, fun Γ' k u ↦ by
        have h := Prove.rootRewriteK_eq G E n Γ' Φ _ _ (prepareRules_eq E rs hrs) k u
        rw [rootRewrite_prepareRules] at h
        simp only [Internal.machineRw, Internal.rootRewriteK_eq]
        rw [h]
        rcases Internal.rootRewrite G E n rs Γ' (Φ.map (Internal.weakenBy k)) u with _ | ⟨u', d⟩
        · rfl
        · rfl⟩ fuel Γ t
  · simp only [↓reduceIte]
    exact Machine.machineReduce_eq (P := ⟨encGlobals G, leaf n, unf', leaf kl, leaf kc, _⟩)
      ⟨rfl, rfl, hunf, rfl, rfl, fun _ _ _ ↦ rfl⟩ fuel Γ t

/-- Whether a number is the label of a leaf of a list of numbers' leaves. -/
theorem any_leaf_eq (j : ℕ) (R : List ℕ) :
    R.any ((fun x : Tree ↦ x.label == j) ∘ leaf) = R.contains j :=
  List.rec rfl (fun r R ih ↦ by
    have e : (r == j) = (j == r) := by
      by_cases h : r = j
      · subst h
        rfl
      · rw [beq_false_of_ne h, beq_false_of_ne (Ne.symm h)]
    simp only [List.any_cons, List.contains_cons, Function.comp_apply, label_leaf, ih, e]) R

/-- The mirror's reduction by the machine at the data of a step, every argument encoded: the
machine's reduction unfolding the definitions of an index below the bound but those excepted, at
rules none of which is a prepared theorem. -/
theorem machineRun_eq (fuel m : ℕ) (except : List ℕ) (kl kc : ℕ) (rs : List NormRule)
    (hrs : Unprepared rs) (Γ : List Tree) (Φ : List Term) (t : Term) :
    «Conversion.machineRun» (encGlobals G) (E.toList.map encEntry) (leaf n)
        [leaf fuel, leaf m, RoseTree.node 0 (except.map leaf), leaf kl, leaf kc,
          RoseTree.node 0 (rs.map encRule)] Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.machineReduceBy G E n (fun j ↦ decide (j < m) && !except.contains j)
        kl kc rs fuel Γ Φ t).map encTerm) := by
  have hunf : ∀ j : ℕ, «Prelude.and» (Const.lt (leaf j) (leaf m))
      («Base.not» («Base.anyT» (fun x ↦ Const.eq x (leaf j)) (except.map leaf))) =
      ofBool (decide (j < m) && !except.contains j) := fun j ↦ by
    rw [(anyT_eq (fun x ↦ Const.eq x (leaf j)) (fun x ↦ x.label == j) _ fun x _ ↦ rfl).trans
      (congrArg ofBool (List.any_map.trans (any_leaf_eq j except)))]
    mirror_simp []
  simp only [«Conversion.machineRun», at_eq, List.getD_cons_zero, List.getD_cons_succ,
    children_eq, RoseTree.children_node, rulesOf_eq]
  exact machineReduceBy_eq G E n _ _ hunf kl kc rs hrs fuel Γ Φ t

/-- The mirror's reduction by the machine agrees with the machine in Lean at the
representations of the checker's data. -/
theorem machineRun_agrees : Internal.Accelerate.Agrees «Conversion.machineRun» :=
  fun G E n d hd Γ Φ t ↦ by
    have h := machineRun_eq G E.toArray n d.fuel d.bound d.except d.kl d.kc d.rules hd Γ Φ t
    rw [List.toList_toArray] at h
    exact h

/-- The function the Lean the compiler emits binds to the reduction by the machine, the machine
in Lean at the representations of the checker's data, is the mirror's reduction: compiled code
that runs it computes what the reduction written in Geb computes, at every argument. -/
theorem machineRun_accel : «Conversion.machineRun$accel» = «Conversion.machineRun» :=
  Internal.Accelerate.machineRun_eq machineRun_agrees

/-- The function bound to the reduction by the machine where the two are to be compared
({name}`Geb.FreeTopos.Internal.Accelerate.machineRunShadow`) is the mirror's reduction as
well. -/
theorem machineRun_shadow :
    Internal.Accelerate.machineRunShadow «Conversion.machineRun» = «Conversion.machineRun» :=
  Internal.Accelerate.machineRunShadow_eq machineRun_agrees

/-! The step of the checker. -/

/-- The label of an encoded certificate's node is its rule's position. -/
theorem label_encConv (l : ConvRule) (cs : List ConvDeriv) :
    (encConv (RoseTree.node l cs)).label = (convData l).1 := by
  rw [encConv_node, RoseTree.label_node]

/-- The first child of an encoded certificate's node is the node of its rule's data. -/
theorem child_encConv (l : ConvRule) (cs : List ConvDeriv) :
    Const.child (encConv (RoseTree.node l cs)) (leaf 0) = RoseTree.node 0 (convData l).2 := by
  rw [encConv_node, child_node]
  rfl

/-- The mirror's hypotheses weakened past a number of new innermost variables. -/
theorem mapT_weakenBy (k : ℕ) (Φ : List Term) :
    «Base.mapT» (fun h ↦ «Derivation.weakenBy» (leaf k) h) (Φ.map encTerm) =
      (Φ.map (Internal.weakenBy k)).map encTerm := by
  simp only [mapT_eq, List.map_map, Function.comp_def, weakenBy_eq]

/-- The mirror's step of the checker at an encoded node is the step of the checker with its
rewriting under weakened hypotheses at the node it encodes, at related results of the
premises. -/
theorem convStep_eq (l : ConvRule) (hl : RulePlain l) (v : DV)
    (xs : List (ConvDeriv × DV × Internal.FastChecks)) (hx : ∀ x ∈ xs, FRel x.2.1 x.2.2) :
    FRel («Conversion.convStep» (encGlobals G) (E.toList.map encEntry) (R.map leaf) (leaf n)
        (encConv (RoseTree.node l (xs.map Prod.fst))) (v :: xs.map fun x ↦ x.2.1))
      (Internal.convFastStep G E R n l (xs.map fun x ↦ (x.1, x.2.2))) := by
  -- the step of the checker of derivations, the premises standing for their rules
  have hbase : ∀ r : Internal.Rule,
      FRel («Derivation.checkStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
          («Conversion.baseNode» (leaf (ruleData r).1) (RoseTree.node 0 (ruleData r).2)
            (encConv (RoseTree.node l (xs.map Prod.fst)))) (v :: xs.map fun x ↦ x.2.1))
        (Internal.fastStep G E n r
          (xs.map fun x ↦ (RoseTree.node x.1.label.toRule [], x.2.2))) := fun r ↦ by
    rw [baseNode_eq]
    have h := checkStep_eq G E n r v
      (xs.map fun x ↦ (RoseTree.node x.1.label.toRule [], x.2.1, x.2.2)) fun y hy ↦ by
        obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hy
        exact hx x hx'
    simpa only [List.map_map, Function.comp_def] using h
  cases l with
  | base r =>
    have hlt := ruleData_lt r
    simp only [«Conversion.convStep», label_eq, label_encConv, child_encConv, convData, lt_leaf,
      label_ne_zero, ofBool_bne, decide_eq_true_eq, hlt, ↓reduceIte, Internal.convFastStep,
      List.map_map, Function.comp_def]
    exact hbase r
  | norm rs fuel =>
    have hn := normalize_eq G E n _ rs (forall₂_rrel hl) fuel
    simp only [«Conversion.convStep», label_eq, label_encConv, child_encConv, convData, lt_leaf,
      eq_leaf, label_ne_zero, ofBool_bne, children_eq, RoseTree.children_node, Nat.reduceLT,
      Nat.reduceBEq, decide_false, Bool.false_eq_true, ↓reduceIte,
      «Conversion.stepNorm», at_eq, List.getD_cons_zero, List.getD_cons_succ, rulesOf_eq,
      template]
    refine ⟨fun Γ k Φ t ↦ ?_, fun Γ Φ φ ↦ ?_⟩
    · simp only [label_leaf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, mapT_weakenBy,
        hn Γ _ t, bindO_eq, Internal.convFastStep, Internal.convStep, ConvRule.hyps,
        Internal.normalizeR_eq]
      cases Internal.normalize G E n rs fuel Γ (Φ.map (Internal.weakenBy k)) t <;> rfl
    · rfl
  | eval rs fuel depth =>
    have he := eval_eq G E n _ rs (forall₂_rrel hl) fuel
    simp only [«Conversion.convStep», label_eq, label_encConv, child_encConv, convData, lt_leaf,
      eq_leaf, label_ne_zero, ofBool_bne, children_eq, RoseTree.children_node, Nat.reduceLT,
      Nat.reduceBEq, decide_false, Bool.false_eq_true, ↓reduceIte,
      «Conversion.stepEval», at_eq, List.getD_cons_zero, List.getD_cons_succ, rulesOf_eq,
      template]
    refine ⟨fun Γ k Φ t ↦ ?_, fun Γ Φ φ ↦ ?_⟩
    · simp only [label_leaf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, mapT_weakenBy,
        he depth Γ _ t, bindO_eq, Internal.convFastStep, Internal.convStep, ConvRule.hyps,
        Internal.evalR_eq, Internal.Reduction.result]
      cases Internal.eval G E n rs fuel depth Γ (Φ.map (Internal.weakenBy k)) t <;> rfl
    · rfl
  | applyMatch j θ =>
    simp only [«Conversion.convStep», label_eq, label_encConv, child_encConv, convData, lt_leaf,
      eq_leaf, label_ne_zero, ofBool_bne, children_eq, RoseTree.children_node, Nat.reduceLT,
      Nat.reduceBEq, decide_false, Bool.false_eq_true, ↓reduceIte,
      «Conversion.stepApply», at_eq, List.getD_cons_zero, List.getD_cons_succ]
    refine ⟨fun Γ k Φ t ↦ rfl, fun Γ Φ φ ↦ ?_⟩
    simp only [label_leaf, applyInst_eq, Internal.convFastStep, Internal.convStep]
    rcases Internal.applyInst E j θ φ with _ | σ
    · rfl
    · have h := (hbase (.apply j θ σ)).2 Γ Φ φ
      simp only [ruleData, Internal.fastStep, List.map_map, Function.comp_def] at h
      simp only [Option.map_some, isSome_eq, Option.isSome_some, ofBool_true, label_leaf,
        get_eq, «Theory.l3», «Theory.l2», single_eq, node_leaf, List.map_map, Function.comp_def,
        bne_iff_ne, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte]
      exact h
  | lit j =>
    have hR : «Base.anyT» (fun x ↦ Const.eq x (leaf j)) (R.map leaf) = ofBool (R.contains j) :=
      (anyT_eq (fun x ↦ Const.eq x (leaf j)) (fun x ↦ x.label == j) _ fun x _ ↦ rfl).trans
        (congrArg ofBool (List.any_map.trans (any_leaf_eq j R)))
    simp only [«Conversion.convStep», label_eq, label_encConv, child_encConv, convData, lt_leaf,
      eq_leaf, label_ne_zero, ofBool_bne, children_eq, RoseTree.children_node, Nat.reduceLT,
      Nat.reduceBEq, decide_false, Bool.false_eq_true, ↓reduceIte,
      «Conversion.stepLit», at_eq, List.getD_cons_zero, hR]
    refine ⟨fun Γ k Φ t ↦ ?_, fun Γ Φ φ ↦ rfl⟩
    simp only [label_leaf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      Literals.litEval_eq, Internal.convFastStep, Internal.convStep]
    cases R.contains j <;> simp [Option.map_map, none_eq, Function.comp_def]
  | machine fuel m except kl kc rs =>
    simp only [«Conversion.convStep», label_eq, label_encConv, child_encConv, convData, lt_leaf,
      eq_leaf, label_ne_zero, ofBool_bne, children_eq, RoseTree.children_node, Nat.reduceLT,
      Nat.reduceBEq, decide_false, Bool.false_eq_true, ↓reduceIte,
      «Conversion.stepMachine», at_eq, List.getD_cons_zero, List.getD_cons_succ, isEmpty_eq,
      List.isEmpty_map]
    refine ⟨fun Γ k Φ t ↦ ?_, fun Γ Φ φ ↦ rfl⟩
    have hΦ : (if rs.isEmpty = true then []
        else «Base.mapT» (fun h ↦ «Derivation.weakenBy» (leaf k) h) (Φ.map encTerm)) =
        (if rs.isEmpty then [] else Φ.map (Internal.weakenBy k)).map encTerm := by
      split
      · rfl
      · exact mapT_weakenBy k Φ
    simp only [label_leaf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hΦ,
      Internal.convFastStep, Internal.convStep, ConvRule.hyps]
    exact machineRun_eq G E n fuel m except kl kc rs hl Γ _ t

/-! The checker. -/

/-- The mirror's checker at an encoded certificate the mirror reads is related to the checker with
its rewriting under weakened hypotheses at the certificate: their rewritings agree at every
context, number of variables and encoded list of hypotheses and term, and their provings at every
context and encoded list of hypotheses and formula. -/
theorem convCheck_fast_eq : ∀ d : ConvDeriv, Plain d →
    FRel («Conversion.convCheck» (encGlobals G) (E.toList.map encEntry) (R.map leaf) (leaf n)
        (encConv d))
      (RoseTree.para (Internal.convFastStep G E R n) d) :=
  RoseTree.ind fun l cs ih hd ↦ by
    obtain ⟨hl, hcs⟩ := plain_node.mp hd
    have h := convStep_eq G E R n l hl
      (Const.para («Conversion.convStep» (encGlobals G) (E.toList.map encEntry) (R.map leaf)
        (leaf n)) (RoseTree.node 0 (convData l).2))
      (cs.map fun c ↦ (c, «Conversion.convCheck» (encGlobals G) (E.toList.map encEntry)
        (R.map leaf) (leaf n) (encConv c), RoseTree.para (Internal.convFastStep G E R n) c))
      (by simpa using fun c hc ↦ ih c hc (hcs c hc))
    simp only [«Conversion.convCheck»] at h ⊢
    rw [encConv_node, Const.para_node, RoseTree.para_node, List.map_cons]
    simpa only [List.map_map, Function.comp_def, encConv_node, List.map_id'] using h

/-- The mirror's checker at an encoded certificate the mirror reads is related to the conversion
checker at the certificate: their rewritings and their provings agree at every context and every
encoded list of hypotheses and term. -/
theorem convCheck_eq (d : ConvDeriv) (hd : Plain d) :
    DRel («Conversion.convCheck» (encGlobals G) (E.toList.map encEntry) (R.map leaf) (leaf n)
        (encConv d))
      (Internal.convCheck G E R n d) :=
  (Internal.para_convFastStep G E R n d).2 ▸ (convCheck_fast_eq G E R n d hd).checks

/-- The mirror's test that an encoded certificate the mirror reads proves an encoded theorem. -/
theorem thmConvChecks_eq (a : Internal.Thm) (d : ConvDeriv) (hd : Plain d) :
    «Conversion.thmConvChecks» (encGlobals G) (E.toList.map encEntry) (R.map leaf) (encThm a)
        (encConv d) =
      ofBool (a.convChecks G E R d) := by
  have hc := (convCheck_eq G E R a.arity d hd).2 a.ctx a.hyps a.concl
  have ha := allT_map («Derivation.isFormula» (encGlobals G) (leaf a.arity) a.ctx) encTerm
    (fun ψ ↦ decide (Internal.typeIn G a.arity a.ctx ψ = some omega)) a.hyps
    fun ψ _ ↦ isFormula_eq G a.arity a.ctx ψ
  mirror_simp [«Conversion.thmConvChecks», Internal.Thm.convChecks, Internal.Thm.wellFormed,
    thArity_eq, thCtx_eq, thHyps_eq, thConcl_eq, allT_isTy, ha, isFormula_eq, hc, ite_leaf_zero,
    Bool.decide_eq_true, Bool.decide_and]
  simp only [Bool.and_assoc]

/-! Developments with certificates. -/

/-- A declaration of a development with certificates as the node of its constructor's position
over its fields. -/
def encConvDecl : Internal.ConvDecl → Tree
  | .base d => RoseTree.node 0 [encDecl d]
  | .conv a c => RoseTree.node 1 [encThm a, encConv c]
  | .ready j => RoseTree.node 2 [leaf j]

/-- The state of the check of a development with certificates as the node of its constants, the
node of its entries and the node of the indices at which the evaluation at literals is ready. -/
def encConvState (s : Internal.ConvState) : Tree :=
  RoseTree.node 0 [encGlobals s.1, RoseTree.node 0 (s.2.1.toList.map encEntry),
    RoseTree.node 0 (s.2.2.map leaf)]

/-- A declaration the mirror reads: a theorem's certificate is one the mirror reads. -/
def DeclPlain : Internal.ConvDecl → Prop
  | .conv _ c => Plain c
  | _ => True

/-- The mirror's state after a declaration of a development with certificates, where its check
accepts it. -/
theorem convDeclStep_eq (d : Internal.ConvDecl) (hd : DeclPlain d) :
    «Conversion.convDeclStep» (encGlobals G) (E.toList.map encEntry) (R.map leaf)
        (encConvDecl d) =
      encOpt ((d.step G E R).map encConvState) := by
  cases d with
  | base b =>
    mirror_simp [«Conversion.convDeclStep», encConvDecl, Internal.ConvDecl.step, declStep_eq]
    rcases b.step G E with _ | ⟨G', E'⟩
    · rfl
    · rfl
  | conv a c =>
    mirror_simp [«Conversion.convDeclStep», encConvDecl, Internal.ConvDecl.step,
      thmConvChecks_eq G E R a c hd, entLang_eq, push_eq]
    cases a.convChecks G E R c
    · rfl
    · simp only [↓reduceIte, Option.map_some, encConvState, Array.toList_push, List.map_append,
        List.map_cons, List.map_nil]
      rfl
  | ready j =>
    mirror_simp [«Conversion.convDeclStep», encConvDecl, Internal.ConvDecl.step, Literals.ready_eq]
    cases Geb.FreeTopos.Literals.ready G E j <;> rfl

/-- The mirror's parts of an encoded state of a development's check. -/
theorem csConsts_eq (s : Internal.ConvState) :
    «Conversion.csConsts» (encConvState s) = encGlobals s.1 := by
  mirror_simp [«Conversion.csConsts», encConvState]

@[inherit_doc csConsts_eq] theorem csEntries_eq (s : Internal.ConvState) :
    «Conversion.csEntries» (encConvState s) = s.2.1.toList.map encEntry := by
  mirror_simp [«Conversion.csEntries», encConvState]

@[inherit_doc csConsts_eq] theorem csIndices_eq (s : Internal.ConvState) :
    «Conversion.csIndices» (encConvState s) = s.2.2.map leaf := by
  mirror_simp [«Conversion.csIndices», encConvState]

/-- The states after declarations from an optional state, by a step that agrees with the check of
each declaration at every optional state. -/
theorem foldl_convDeclStep {f : Tree → Tree → Tree} (ds : List Internal.ConvDecl)
    (hf : ∀ d ∈ ds, ∀ o : Option Internal.ConvState,
      f (encOpt (o.map encConvState)) (encConvDecl d) =
        encOpt ((o.bind fun st ↦ d.step st.1 st.2.1 st.2.2).map encConvState)) :
    ∀ o : Option Internal.ConvState,
      (ds.map encConvDecl).foldl f (encOpt (o.map encConvState)) =
        encOpt ((o.bind fun s ↦
          ds.foldlM (fun st d ↦ d.step st.1 st.2.1 st.2.2) s).map encConvState) :=
  ds.rec (motive := fun ds ↦ (∀ d ∈ ds, ∀ o : Option Internal.ConvState,
      f (encOpt (o.map encConvState)) (encConvDecl d) =
        encOpt ((o.bind fun st ↦ d.step st.1 st.2.1 st.2.2).map encConvState)) →
      ∀ o : Option Internal.ConvState,
        (ds.map encConvDecl).foldl f (encOpt (o.map encConvState)) =
          encOpt ((o.bind fun s ↦
            ds.foldlM (fun st d ↦ d.step st.1 st.2.1 st.2.2) s).map encConvState))
    (fun _ o ↦ by cases o <;> rfl)
    (fun d ds ih hf o ↦ by
      rw [List.map_cons, List.foldl_cons, hf d List.mem_cons_self o,
        ih (fun d' hd' ↦ hf d' (List.mem_cons_of_mem d hd'))]
      cases o with
      | none => rfl
      | some st =>
        simp only [Option.bind_some, List.foldlM_cons]
        rfl) hf

/-- The mirror's state after a development with certificates, each declaration checked with the
state the declarations before it leave, at declarations the mirror reads. -/
theorem checkConvDev_eq (ds : List Internal.ConvDecl) (hds : ∀ d ∈ ds, DeclPlain d) :
    «Conversion.checkConvDev» (encGlobals G) (E.toList.map encEntry) (ds.map encConvDecl) =
      encOpt ((Internal.checkConvDev G E ds).map encConvState) := by
  simp only [«Conversion.checkConvDev», template, reverse_eq, foldr_eq, List.foldr_reverse]
  refine foldl_convDeclStep ds (fun d hd o ↦ ?_) (some (G, E, []))
  cases o with
  | none => rfl
  | some st =>
    obtain ⟨G', E', R'⟩ := st
    have h := convDeclStep_eq G' E' R' d (hds d hd)
    mirror_simp [csConsts_eq, csEntries_eq, csIndices_eq, h]

end GebTests.Prototypes.FreeTopos.Agreement.Conversion

end
