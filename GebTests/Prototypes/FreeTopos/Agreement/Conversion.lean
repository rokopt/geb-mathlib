/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Literals
public import GebTests.Prototypes.FreeTopos.Agreement.Prove
public import Geb.Prototypes.FreeTopos.Internal.Conversion

set_option doc.verso true in
/-!
# The conversion checker written in Geb

The functions of {lit}`bootstrap/free-topos/conversion.geb`, in the Lean the bootstrap compiler
emits ({lit}`GebMirror.Metalogic`), agree with the checker of the internal language with a step
of conversion ({name}`Geb.FreeTopos.Internal.convCheck`) at every encoded certificate whose rules
the mirror reads: the rule of the language a certificate's root stands for, the rules of the
normalizer a step names, the instance of a theorem whose conclusion matches a formula, the step
of the checker at a node and the checker, so that the two checkers accept the same certificates
of the same theorems.

A certificate is encoded as a derivation is, the node of its rule's position over the node of the
rule's data and its premises: a rule of the language at its position and with its data, and the
steps of conversion and the application of a theorem at the positions after the language's rules.
A rule of the normalizer that holds a prepared theorem holds a matching, a function, which no
tree encodes, so that the agreement is stated at the certificates none of whose steps names one;
a step of the prover's reductions names its rules before they are prepared.

## Main definitions

* {lit}`convData`, {lit}`encConv` — the encoding of a rule of the certificates and of a
  certificate.
* {lit}`RulePlain`, {lit}`Plain` — the rules of the certificates the mirror reads, and the
  certificates of such rules.

## Main statements

* {lit}`toRule_eq` — the mirror's rule of the language a certificate's root stands for.
* {lit}`applyInst_eq` — the mirror's instance of a theorem whose conclusion matches a formula.
* {lit}`convStep_eq` — the mirror's step of the checker.
* {lit}`convCheck_eq` — the mirror's checker.
* {lit}`thmConvChecks_eq` — the mirror's test that a certificate proves a theorem.

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

/-- A rule of the certificates the mirror reads: a step of the prover's reductions names no
prepared theorem, and the rule is not the reduction by the machine. -/
def RulePlain : ConvRule → Prop
  | .norm rs _ | .eval rs _ _ => Unprepared rs
  | .machine _ _ _ _ _ _ => False
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
  simp only [«Conversion.rulesOf», «Conversion/RuleAt.map», foldr_eq]
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
  | machine fuel m except kl kc rs => exact hl.elim

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

end GebTests.Prototypes.FreeTopos.Agreement.Conversion

end
