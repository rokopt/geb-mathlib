/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Prove
public import GebTests.Prototypes.FreeTopos.Agreement.Translation
public import Geb.Prototypes.FreeTopos.Tactics

set_option doc.verso true in
/-!
# The tactics written in Geb

The functions of {lit}`bootstrap/free-topos/tactics.geb`, in the Lean the bootstrap compiler emits
({lit}`GebMirror.Metalogic`), agree with the tactics of the internal language
({lit}`Geb.FreeTopos.Tactics`) at every encoded input: the proofs by reduction, by induction and
case analysis, with hypotheses, by search and about the translation's trees, each at related
rules and provers, so that the tactics written in Geb construct exactly the derivations the Lean
tactics construct.

## Main definitions

* {lit}`KRel`, {lit}`MSRel` — the relations of the mirror's provers from rules, and provers from
  added rules and provers from rules, to Lean's.
* {lit}`ARel`, {lit}`IRel`, {lit}`SkipRel` — the relations of the mirror's derivations from
  hypotheses and added rules or indices, and of its predicates on variables, to Lean's.
* {lit}`encMask` — the encoding of a rewriting under a mask.

## Main statements

* {lit}`byMode_eq`, {lit}`byNF_eq`, {lit}`normH_eq` — the proofs by reduction agree.
* {lit}`byListIndWeak_eq`, {lit}`byListSplit_eq`, {lit}`bitsInd_eq` and the proofs by induction
  and case analysis beside them agree.
* {lit}`withWeakHyps_eq`, {lit}`withInsts_eq`, {lit}`withChildHyps_eq`, {lit}`byImpI_eq` and the
  proofs with hypotheses beside them agree.
* {lit}`matchesWith_eq`, {lit}`byInstsOnce_eq`, {lit}`byInsts_eq`, {lit}`byAuto_eq` — the
  instance search and the proof by search agree.
* {lit}`occRewrite_eq`, {lit}`abstractTerm_eq`, {lit}`byTreeSplit_eq`, {lit}`byAutoT_eq`,
  {lit}`byAutoC_eq`, {lit}`maskSub_eq`, {lit}`byMaskSubs_eq`, {lit}`byGeneralize_eq` — the
  tactics about the translation's trees agree.

## Tags

prover, tactic, internal language, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Tactics

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Fold GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.Language
  GebTests.Prototypes.FreeTopos.Agreement.Derivation
  GebTests.Prototypes.FreeTopos.Agreement.Prove
open Internal (Term Deriv NormRule)
open scoped FinEnum

/-! The connectives. -/

/-- The mirror's truth of the connectives from an index. -/
@[simp] theorem ttL_eq (o : ℕ) :
    «Tactics.ttL» (leaf o) = encTerm (Internal.Logic.tt o) :=
  mDefn_eq o [] []

/-- The mirror's implication of the connectives from an index. -/
@[simp] theorem impL_eq (o : ℕ) (p q : Term) :
    «Tactics.impL» (leaf o) (encTerm p) (encTerm q) =
      encTerm (Internal.Logic.imp o p q) :=
  mDefn_eq (o + 2) [] [q, p]

/-- The mirror's proof of truth. -/
@[simp] theorem trueI_eq : «Tactics.trueI» = encDeriv Internal.Logic.trueI := by
  simp only [«Tactics.trueI», Internal.Logic.trueI, Internal.Logic.nd, encDeriv_node,
    ruleData, «Prover.dNode», «Theory.l2», «Language.mNode»,
    single_eq, List.map_cons, List.map_nil, node_leaf]

/-- The mirror's introduction of an implication. -/
@[simp] theorem impI_eq (j n : ℕ) (p q : Term) (d : Deriv) :
    «Tactics.impI» (leaf j) (leaf n) (encTerm p) (encTerm q) (encDeriv d) =
      encDeriv (Internal.Logic.impI j n p q d) := by
  simp only [«Tactics.impI», Internal.Logic.impI, Internal.Logic.nd, encDeriv_node,
    ruleData, «Prover.dNode», «Theory.l2», «Theory.l3»,
    «Prelude.single», «Language.mNode», List.map_cons, List.map_nil,
    node_leaf, add_leaf]

/-! Proofs by reduction. -/

/-- The mirror's application of an encoded term to encoded arguments, the first first. -/
@[simp] theorem mApps_eq (f : Term) (xs : List Term) :
    «Tactics.mApps» (encTerm f) (xs.map encTerm) = encTerm (Tactics.apps f xs) := by
  simp only [«Tactics.mApps», foldr_eq, Tactics.apps]
  revert f
  exact xs.rec (fun _ ↦ rfl) fun x xs ih f ↦ by
    simp only [List.map_cons, List.foldr_cons, List.foldl_cons, mApp_eq]
    exact ih _

/-- The mirror's proof by reducing both sides to one normal form at a depth, at related rules. -/
theorem byMode_eq (m : Internal.Depth) (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) :
    PRel («Tactics.byMode» (leaf (encDepth m)) (encGlobals G) (E.toList.map encEntry)
        (leaf n) rs')
      (Tactics.byMode m G E n rs) := fun Γ Φ t u ↦
  joinBy_eq _ _ (eval_eq G E n rs' rs hrs 4096 m) Γ Φ t u

/-- The mirror's proof by reducing both sides to one weak normal form. -/
theorem byWeak_eq (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) :
    PRel («Tactics.byWeak» (encGlobals G) (E.toList.map encEntry) (leaf n) rs')
      (Tactics.byWeak G E n rs) :=
  byMode_eq .weak G E n rs' rs hrs

/-- The simplification of the mirror's tactics: the options, lists and pairs of the program, the
derivations' nodes and the terms' builders, and the given lemmas. -/
local macro "tac_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [bindO_eq, mapO_eq, children_eq, RoseTree.children_node, lcase_cons, lcase_nil,
    Option.bind_eq_bind, Option.pure_def, Option.map_bind, Option.bind_map, Option.map_map,
    Option.elim_some, Option.elim_none, Option.map_some, Option.map_none, Option.bind_some,
    Option.bind_none, Function.comp_def, none_eq, some_eq, elim_encOpt, p1_encTDB, p2_encTDB,
    p1_encDB, p2_encDB, encDeriv_node, ruleData, «Prover.dNode»,
    «Language.mNode», «Theory.l2», «Theory.l3»,
    «Theory.l4», single_eq, node_leaf, List.map_cons, List.map_nil, mapT_weaken1,
    mapT_weaken2, length_eq, List.length_map, mApp_eq, mVar_eq, weaken1_eq, weaken2_eq, mEq_eq,
    nth_eq, abstractVar_eq, List.getElem?_map, $ls,*])

/-- The mirror's proof of an equation by that of its sides' normal forms at a depth, at related
rules and a related prover. -/
theorem byNF_eq (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (m : Internal.Depth)
    (p' : List Tree → List Tree → Tree → Tree → Tree) (p : Internal.Prover) (hp : PRel p' p) :
    PRel («Tactics.byNF» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (leaf (encDepth m)) p')
      (Tactics.byNF G E n rs m p) := by
  have hp' : ∀ Γ Φ t u, p' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p Γ Φ t u).map encDeriv) := hp
  have hE : ∀ Γ Φ t, «Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
      (leaf 4096) (leaf (encDepth m)) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.eval G E n rs 4096 m Γ Φ t).map encTDB) :=
    eval_eq G E n rs' rs hrs 4096 m
  intro Γ Φ t u
  simp only [«Tactics.byNF», Tactics.byNF, hE]
  rcases Internal.eval G E n rs 4096 m Γ Φ t with _ | ⟨t', dt, _⟩
  · rfl
  rcases Internal.eval G E n rs 4096 m Γ Φ u with _ | ⟨u', du, _⟩
  · tac_simp []
  tac_simp [hp']
  rcases p Γ Φ t' u' <;> rfl

/-- The mirror's rules of the hypotheses below a number. -/
theorem hypRules_rel (k : ℕ) :
    List.Forall₂ RRel («Tactics.hypRules» (leaf k))
      ((List.range k).map NormRule.hyp) := by
  simp only [«Tactics.hypRules», range_eq, foldr_eq, List.foldr_map]
  exact (List.range k).rec List.Forall₂.nil fun i is ih ↦ by
    simp only [List.foldr_cons, List.map_cons]
    exact List.Forall₂.cons rfl ih

/-- The mirror's appending of lists of rules. -/
@[simp] theorem appendNR_eq (xs ys : List (Tree × (Tree → Tree → List Tree → Tree))) :
    «Tactics.appendNR» xs ys = xs ++ ys := by
  simp only [«Tactics.appendNR», foldr_eq]
  exact xs.rec rfl fun x xs ih ↦ by rw [List.foldr_cons, ih]; rfl

/-- The mirror's proof by normalization, weak head normal forms first, with the hypotheses as
rewriting rules, at related rules. -/
theorem normH_eq (G : Internal.Globals) (E : Array Internal.Entry)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) :
    PRel («Tactics.normH» (encGlobals G) (E.toList.map encEntry) rs')
      (Tactics.normH G E rs) := fun Γ Φ t u ↦ by
  simp only [«Tactics.normH», Tactics.normH, length_eq, List.length_map, appendNR_eq]
  exact byNormW_eq G E 0 _ _ (List.rel_append (hypRules_rel Φ.length) hrs) 1024 Γ Φ t u

/-! Proofs by induction and case analysis. -/

/-- The mirror's prover under new variables of the statement's arguments, at a related prover. -/
theorem funExts_eq (k : ℕ) (G : Internal.Globals)
    (p' : List Tree → List Tree → Tree → Tree → Tree) (p : Internal.Prover) (hp : PRel p' p) :
    PRel («Tactics.funExts» (leaf k) (encGlobals G) p') (Tactics.funExts k G p) := by
  simp only [«Tactics.funExts», iter_leaf, Tactics.funExts]
  exact Nat.rec hp (fun k ih ↦ by
    rw [Nat.repeat, List.replicate_succ, List.foldr_cons]
    exact byFunExt_eq G 0 _ _ ih) k

/-- The mirror's proof by induction on a list in the form of the uniqueness of its fold, each
premise by weak reduction, at related rules. -/
theorem byListIndWeak_eq (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ) (s : Term)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) :
    PRel («Tactics.byListIndWeak» (encGlobals G) (E.toList.map encEntry) (leaf n)
        (encTerm s) rs')
      (Tactics.byListIndWeak G E n s rs) := by
  have hW : ∀ Γ Φ t u, «Tactics.byWeak» (encGlobals G) (E.toList.map encEntry)
      (leaf n) rs' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Tactics.byWeak G E n rs Γ Φ t u).map encDeriv) := byWeak_eq G E n rs' rs hrs
  intro Γ Φ t u
  rcases Γ with _ | ⟨c, Γ'⟩
  · rfl
  simp only [«Tactics.byListIndWeak», Tactics.byListIndWeak, listPart_eq]
  tac_simp []
  rcases Internal.listPart c with _ | a
  · rfl
  tac_simp [lowerHyps_eq]
  rcases Internal.lowerHyps G n Γ' Φ with _ | Φ'
  · rfl
  tac_simp [hW, instAt_eq, listConsAt_eq, weakenElem_eq, subst_atVar0]
  simp only [Option.map_eq_bind, Function.comp_def]

/-- The mirror's proof by induction on a rose tree alone in the form of the uniqueness of its
fold, each premise by a related prover. -/
theorem byRoseIndWith_eq (G : Internal.Globals) (n : ℕ) (s : Term)
    (p' : List Tree → List Tree → Tree → Tree → Tree) (p : Internal.Prover) (hp : PRel p' p) :
    PRel («Tactics.byRoseIndWith» (encGlobals G) (leaf n) (encTerm s) p')
      (Tactics.byRoseIndWith G n s p) := by
  have hp' : ∀ Γ t u, p' Γ [] (encTerm t) (encTerm u) = encOpt ((p Γ [] t u).map encDeriv) :=
    fun Γ t u ↦ hp Γ [] t u
  intro Γ Φ t u
  rcases Γ with _ | ⟨r, _ | ⟨r', Γ'⟩⟩ <;>
    simp only [«Tactics.byRoseIndWith», Tactics.byRoseIndWith]
  · rfl
  · mirror_simp [roseLabel_eq, typeIn_eq, Theory.mirror_list, «Theory.l4»,
      «Theory.l2», Option.bind_eq_bind]
    rcases Internal.roseParts r with _ | ⟨a, f⟩
    · rfl
    rcases Internal.typeIn G n [r] t with _ | C
    · rfl
    tac_simp [roseNodeAt_eq, roseMapAt_eq, subst_atVar0, hp']
    simp only [Option.map_eq_bind, Function.comp_def]
  · mirror_simp [beq_iff_eq, Nat.reduceEqDiff, none_eq]

/-- The mirror's derivation of an equation from the equation of its sides' abstractions over a
term, by applying them to the term. -/
theorem applyAbs_eq (x : Term) (k : ℕ) (F H : Term) (d : Deriv) :
    «Tactics.applyAbs» (encTerm x) (leaf k) (encTerm F) (encTerm H) (encDeriv d) =
      encDeriv (RoseTree.node (.cut (Term.eq F H)) [d, RoseTree.node
        (.convFrom (Term.eq (Term.app F x) (Term.app H x)))
        [RoseTree.node .cong [RoseTree.node .beta [], RoseTree.node .beta []],
          RoseTree.node .join [RoseTree.node .cong [RoseTree.node (.rwHyp k false) [],
            RoseTree.node .refl []], RoseTree.node .refl []]]]) := by
  simp only [«Tactics.applyAbs»]
  tac_simp []
  rfl

/-- The mirror's proof by case analysis of a list variable, each case by its related prover. -/
theorem byListSplit_eq (G : Internal.Globals) (n i : ℕ)
    (p₀' p₁' : List Tree → List Tree → Tree → Tree → Tree) (p₀ p₁ : Internal.Prover)
    (hp₀ : PRel p₀' p₀) (hp₁ : PRel p₁' p₁) :
    PRel («Tactics.byListSplit» (encGlobals G) (leaf n) (leaf i) p₀' p₁')
      (Tactics.byListSplit G n i p₀ p₁) := by
  have hL : ∀ Γ Φ t u, «Prover.byListIndWith» (encGlobals G) (leaf n) (leaf 0) (leaf 1)
      p₀' p₁' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byListIndWith G n 0 1 p₀ p₁ Γ Φ t u).map encDeriv) :=
    byListIndWith_eq G n 0 1 _ _ _ _ hp₀ hp₁
  intro Γ Φ t u
  simp only [«Tactics.byListSplit», Tactics.byListSplit]
  tac_simp []
  rcases Γ[i]? with _ | c
  · rfl
  tac_simp [hL, applyAbs_eq]
  rcases Internal.byListIndWith G n 0 1 p₀ p₁ (c :: Γ) (Φ.map Internal.weaken1) _ _ <;> rfl

/-- The mirror's proof by case analysis of a coproduct variable, each case by its related
prover. -/
theorem bySplit2_eq (kl kr i : ℕ) (p₀' p₁' : List Tree → List Tree → Tree → Tree → Tree)
    (p₀ p₁ : Internal.Prover) (hp₀ : PRel p₀' p₀) (hp₁ : PRel p₁' p₁) :
    PRel («Tactics.bySplit2» (leaf kl) (leaf kr) (leaf i) p₀' p₁')
      (Tactics.bySplit2 kl kr i p₀ p₁) := by
  have hp₀' : ∀ Γ Φ t u, p₀' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p₀ Γ Φ t u).map encDeriv) := hp₀
  have hp₁' : ∀ Γ Φ t u, p₁' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p₁ Γ Φ t u).map encDeriv) := hp₁
  intro Γ Φ t u
  simp only [«Tactics.bySplit2», Tactics.bySplit2]
  tac_simp []
  rcases Γ[i]? with _ | c
  · rfl
  tac_simp [coprodParts_eq]
  rcases Internal.coprodParts c with _ | ⟨a, b⟩
  · rfl
  tac_simp [p1_eq, p2_eq, mArr_eq, hp₀', hp₁', applyAbs_eq]
  rcases p₀ (a :: Γ) (Φ.map Internal.weaken1) _ _ with _ | q₀
  · rfl
  rcases p₁ (b :: Γ) (Φ.map Internal.weaken1) _ _ with _ | q₁ <;> rfl

/-- The mirror's proof by case analysis of the innermost list variable, each case by a related
prover. -/
theorem byListCases_eq (G : Internal.Globals) (n : ℕ)
    (p' : List Tree → List Tree → Tree → Tree → Tree) (p : Internal.Prover) (hp : PRel p' p) :
    PRel («Tactics.byListCases» (encGlobals G) (leaf n) p')
      (Tactics.byListCases G n p) :=
  byListIndWith_eq G n 0 1 _ _ _ _ hp hp

/-- The mirror's proof by induction on a bitstring, each case by its related prover. -/
theorem bitsInd_eq (G : Internal.Globals) (n : ℕ)
    (p₀' p₁' : List Tree → List Tree → Tree → Tree → Tree) (p₀ p₁ : Internal.Prover)
    (hp₀ : PRel p₀' p₀) (hp₁ : PRel p₁' p₁) :
    PRel («Tactics.bitsInd» (encGlobals G) (leaf n) p₀' p₁')
      (Tactics.bitsInd G n p₀ p₁) :=
  byListIndWith_eq G n 0 1 _ _ _ _ hp₀ (bySplit_eq 3 4 1 _ _ hp₁)

/-- The mirror's proof by case analysis of the innermost bitstring variable, each case by a
related prover. -/
theorem bitsCases_eq (G : Internal.Globals) (n : ℕ)
    (p' : List Tree → List Tree → Tree → Tree → Tree) (p : Internal.Prover) (hp : PRel p' p) :
    PRel («Tactics.bitsCases» (encGlobals G) (leaf n) p') (Tactics.bitsCases G n p) :=
  bitsInd_eq G n _ _ _ _ hp hp

/-- The mirror's proof by case analysis of a bitstring variable to a number of bits, each case by
a related prover. -/
theorem byBits_eq (G : Internal.Globals) (p' : List Tree → List Tree → Tree → Tree → Tree)
    (p : Internal.Prover) (hp : PRel p' p) (d i : ℕ) :
    PRel («Tactics.byBits» (encGlobals G) p' (leaf d) (leaf i))
      (Tactics.byBits G p d i) := by
  simp only [«Tactics.byBits», iter_leaf, Tactics.byBits]
  revert i
  exact Nat.rec (fun _ ↦ hp) (fun d ih i ↦ by
    rw [Nat.repeat]
    exact byListSplit_eq G 0 i _ _ _ _ hp (bySplit2_eq 3 4 1 _ _ _ _ (ih 1) (ih 1))) d

/-- The mirror's proof by case analysis of a list variable to three elements, at related
provers. -/
theorem byLength3_eq (G : Internal.Globals) (i : ℕ)
    (p' q' : List Tree → List Tree → Tree → Tree → Tree) (p q : Internal.Prover)
    (hp : PRel p' p) (hq : PRel q' q) :
    PRel («Tactics.byLength3» (encGlobals G) (leaf i) p' q')
      (Tactics.byLength3 G i p q) :=
  byListSplit_eq G 0 i _ _ _ _ hq (byListSplit_eq G 0 0 _ _ _ _ hq
    (byListSplit_eq G 0 0 _ _ _ _ hq (byListSplit_eq G 0 0 _ _ _ _ hp hq)))

/-! Proofs with hypotheses. -/

/-- The mirror's provers from rules and provers from rules are related when they are related
provers at related rules. -/
def KRel (k' : List (Tree × (Tree → Tree → List Tree → Tree)) →
      List Tree → List Tree → Tree → Tree → Tree)
    (k : List NormRule → Internal.Prover) : Prop :=
  ∀ rs' rs, List.Forall₂ RRel rs' rs → PRel (k' rs') (k rs)

/-- The mirror's derivations from hypotheses and added rules and derivations from them are
related when they agree at every list of encoded hypotheses and related added rules. -/
def ARel (a' : List Tree → List (Tree × (Tree → Tree → List Tree → Tree)) → Tree)
    (a : List Term → List NormRule → Option Deriv) : Prop :=
  ∀ Φ₁ ex' ex, List.Forall₂ RRel ex' ex → a' (Φ₁.map encTerm) ex' = encOpt ((a Φ₁ ex).map encDeriv)

/-- The mirror's rule of the hypothesis of an index. -/
theorem hypRule_rel (i : ℕ) : RRel («Tactics.hypRule» (leaf i)) (.hyp i) := rfl

/-- The mirror's proof with hypotheses cut in in normal form and used as rewriting rules before
those given to a related prover from rules, at related rules. -/
theorem withWeakHyps_eq (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (is : List ℕ)
    (k' : List (Tree × (Tree → Tree → List Tree → Tree)) →
      List Tree → List Tree → Tree → Tree → Tree)
    (k : List NormRule → Internal.Prover) (hk : KRel k' k) (m : Internal.Depth) :
    PRel («Tactics.withWeakHyps» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (is.map leaf) k' (leaf (encDepth m)))
      (Tactics.withWeakHyps G E n rs is k m) := by
  have hE : ∀ Γ Φ t, «Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
      (leaf 4096) (leaf (encDepth m)) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.eval G E n rs 4096 m Γ Φ t).map encTDB) :=
    eval_eq G E n rs' rs hrs 4096 m
  intro Γ Φ t u
  simp only [«Tactics.withWeakHyps», Tactics.withWeakHyps, foldr_eq]
  refine (?_ : ARel _ _) Φ [] [] .nil
  refine List.rel_foldr (R := fun (i' : Tree) (i : ℕ) ↦ i' = leaf i)
    (fun i' i hi a' a ha ↦ ?_) (fun Φ₁ ex' ex hex ↦ hk ex' ex hex Γ Φ₁ t u)
    (List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun _ _ ↦ rfl))
  subst hi
  intro Φ₁ ex' ex hex
  tac_simp [eqParts_eq]
  rcases Φ₁[i]? with _ | φ
  · rfl
  tac_simp [eqParts_eq]
  rcases Internal.eqParts φ with _ | ⟨a₀, b₀⟩
  · rfl
  tac_simp [p1_eq, p2_eq, hE]
  rcases Internal.eval G E n rs 4096 m Γ Φ₁ a₀ with _ | ⟨a₁, da, _⟩
  · rfl
  tac_simp [hE]
  rcases Internal.eval G E n rs 4096 m Γ Φ₁ b₀ with _ | ⟨b₁, db, _⟩
  · rfl
  have hr := ha (Φ₁ ++ [Term.eq a₁ b₁]) _ _
    (List.rel_append hex (.cons (hypRule_rel Φ₁.length) .nil))
  simp only [List.map_append, List.map_cons, List.map_nil] at hr
  tac_simp [appendNR_eq, append_eq, hr]
  simp only [Option.map_eq_bind, Function.comp_def]

/-- The mirror's proof by induction on a list with the induction hypothesis in weak normal form
as a rewriting rule, at related rules. -/
theorem byListIndHypWeak_eq (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) :
    PRel («Tactics.byListIndHypWeak» (encGlobals G) (E.toList.map encEntry) (leaf n)
        rs')
      (Tactics.byListIndHypWeak G E n rs) := by
  simp only [«Tactics.byListIndHypWeak», Tactics.byListIndHypWeak]
  refine byListIndWith_eq G n 0 1 _ _ _ _ (byWeak_eq G E n rs' rs hrs) fun Γ Φ t u ↦ ?_
  have h := withWeakHyps_eq G E n rs' rs hrs [Φ.length - 1] _ _
    (fun ex' ex hex ↦ byWeak_eq G E n _ _ (List.rel_append hex hrs)) .weak Γ Φ t u
  simp only [length_eq, List.length_map, sub_leaf, single_eq, appendNR_eq, List.map_cons,
    List.map_nil, encDepth] at h ⊢
  exact h

/-- The mirror's proof by induction on a bitstring with the induction hypothesis in normal form
as a rewriting rule, the construction's case by case analysis of its bit, at related rules. -/
theorem byBitsIndHyp_eq (G : Internal.Globals) (E : Array Internal.Entry)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (m : Internal.Depth) :
    PRel («Tactics.byBitsIndHyp» (encGlobals G) (E.toList.map encEntry) rs'
        (leaf (encDepth m)))
      (Tactics.byBitsIndHyp G E rs m) := by
  simp only [«Tactics.byBitsIndHyp», Tactics.byBitsIndHyp]
  refine byListIndWith_eq G 0 0 1 _ _ _ _ (byMode_eq m G E 0 rs' rs hrs) <|
    bySplit_eq 3 4 1 _ _ fun Γ Φ t u ↦ ?_
  have h := withWeakHyps_eq G E 0 rs' rs hrs [Φ.length - 1] _ _
    (fun ex' ex hex ↦ byMode_eq m G E 0 _ _ (List.rel_append hex hrs)) m Γ Φ t u
  simp only [length_eq, List.length_map, sub_leaf, single_eq, appendNR_eq, List.map_cons,
    List.map_nil] at h ⊢
  exact h

/-- The mirror's rewriting of the function of an application to arguments by a hypothesis. -/
@[simp] theorem rwFun_eq (i k : ℕ) :
    «Tactics.rwFun» (leaf i) (leaf k) = encDeriv (Tactics.rwFun i k) := by
  simp only [«Tactics.rwFun», iter_leaf, Tactics.rwFun]
  exact Nat.rec (by tac_simp []; rfl) (fun k ih ↦ by
    rw [Nat.repeat, ih]
    tac_simp []) k

/-- The mirror's equations of the applications of two encoded functions to encoded lists of
arguments. -/
@[simp] theorem instEqs_eq (F H : Term) (αs : List (List Term)) :
    «Tactics.instEqs» (encTerm F) (encTerm H) (αs.map (·.map encTerm)) =
      (Tactics.instEqs F H αs).map encTerm := by
  simp only [«Tactics.instEqs», foldr_eq, Tactics.instEqs]
  exact αs.rec rfl fun α αs ih ↦ by
    simp only [List.map_cons, List.foldr_cons, ih, mApps_eq, mEq_eq]

/-- The instances' equations are as many as the lists of arguments. -/
@[simp] theorem length_instEqs (F H : Term) (αs : List (List Term)) :
    (Tactics.instEqs F H αs).length = αs.length :=
  List.length_map _

/-- The mirror's derivation under the equations of the instances, each cut in. -/
@[simp] theorem cutInsts_eq (F H : Term) (i : ℕ) (αs : List (List Term)) (rest : Deriv) :
    «Tactics.cutInsts» (encTerm F) (encTerm H) (leaf i) (αs.map (·.map encTerm))
        (encDeriv rest) =
      encDeriv (Tactics.cutInsts F H i αs rest) := by
  simp only [«Tactics.cutInsts», foldr_eq, Tactics.cutInsts]
  exact αs.rec rfl fun α αs ih ↦ by
    simp only [List.map_cons, List.foldr_cons, ih]
    tac_simp [mApps_eq, rwFun_eq]

/-- The mirror's proof with the instances of a hypothesis equating functions, cut in and in normal
form as rewriting rules before those given to a related prover from rules, at related rules. -/
theorem withInsts_eq (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (h : ℕ) (αs : List (List Term))
    (k' : List (Tree × (Tree → Tree → List Tree → Tree)) →
      List Tree → List Tree → Tree → Tree → Tree)
    (k : List NormRule → Internal.Prover) (hk : KRel k' k) (m : Internal.Depth) :
    PRel («Tactics.withInsts» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (leaf h) (αs.map (·.map encTerm)) k' (leaf (encDepth m)))
      (Tactics.withInsts G E n rs h αs k m) := by
  intro Γ Φ t u
  simp only [«Tactics.withInsts», Tactics.withInsts]
  tac_simp [eqParts_eq]
  rcases Φ[h]? with _ | φ
  · rfl
  tac_simp [eqParts_eq]
  rcases Internal.eqParts φ with _ | ⟨F, H⟩
  · rfl
  have hw := withWeakHyps_eq G E n rs' rs hrs ((List.range αs.length).map (Φ.length + ·)) k' k
    hk m Γ (Φ ++ Tactics.instEqs F H αs) t u
  simp only [List.map_append, List.map_map, Function.comp_def] at hw
  tac_simp [p1_eq, p2_eq, instEqs_eq, append_eq, range_eq, add_leaf, mapT_eq, List.map_map,
    length_instEqs, hw, cutInsts_eq]
  simp only [Option.map_eq_bind, Function.comp_def]

/-- The mirror's application of a definition of the translation's library, the arguments the
first first. -/
@[simp] theorem call_eq (k : ℕ) (θ : List Tree) (args : List Term) :
    «Translation.call» (leaf k) θ (args.map encTerm) =
      encTerm (Translation.call k θ args) := by
  simp only [«Translation.call», reverse_eq, ← List.map_reverse, mDefn_eq, Translation.call]

/-- The mirror's element of a list of formulas at a position. -/
@[simp] theorem nthOf_eq (X : Term) (p : ℕ) :
    «Tactics.nthOf» (encTerm X) (leaf p) = encTerm (Tactics.nthOf X p) := by
  have h : ∀ p : ℕ, Nat.repeat (fun Y ↦ «Translation.call» (leaf 7) [omega] [Y]) p
      (encTerm X) =
      encTerm (p.rec X fun _ Y ↦ Translation.call Translation.D.tail [omega] [Y]) :=
    Nat.rec rfl fun p ih ↦ by
      rw [Nat.repeat, ih]
      exact call_eq Translation.D.tail [omega] [_]
  simp only [«Tactics.nthOf», iter_leaf, single_eq, «Theory.l2», h,
    mStar_eq, mEq_eq, Tactics.nthOf, Theory.mirror_omega]
  exact call_eq Translation.D.headD [omega] [_, _]

/-- The mirror's derivations from hypotheses and indices of instances and derivations from them
are related when they agree at every list of encoded hypotheses and indices. -/
def IRel (a' : List Tree → List Tree → Tree) (a : List Term → List ℕ → Option Deriv) : Prop :=
  ∀ Φ₁ is, a' (Φ₁.map encTerm) (is.map leaf) = encOpt ((a Φ₁ is).map encDeriv)

/-- The mirror's proof with the hypotheses at the children of an induction on rose trees and
their instances, at related rules, arguments and prover from indices of instances. -/
theorem withChildHyps_eq (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (h : ℕ) (kids : List ℕ)
    (args' : Tree → List (List Tree)) (args : ℕ → List (List Term))
    (hargs : ∀ p, args' (leaf p) = (args p).map (·.map encTerm))
    (k' : List Tree → List Tree → List Tree → Tree → Tree → Tree)
    (k : List ℕ → Internal.Prover) (hk : ∀ is, PRel (k' (is.map leaf)) (k is)) :
    PRel («Tactics.withChildHyps» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (leaf h) (kids.map leaf) args' k')
      (Tactics.withChildHyps G E n rs h kids args k) := by
  have hE : ∀ Γ Φ t, «Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf n)
      rs' (leaf 4096) (leaf 1) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.eval G E n rs 4096 .weak Γ Φ t).map encTDB) :=
    eval_eq G E n rs' rs hrs 4096 .weak
  have hEh : ∀ Γ Φ t, «Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf n)
      [«Tactics.hypRule» (leaf h)] (leaf 4096) (leaf 1) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.eval G E n [.hyp h] 4096 .weak Γ Φ t).map encTDB) :=
    eval_eq G E n _ _ (.cons (hypRule_rel h) .nil) 4096 .weak
  intro Γ Φ t u
  simp only [«Tactics.withChildHyps», Tactics.withChildHyps, foldr_eq]
  tac_simp [eqParts_eq]
  rcases Φ[h]? with _ | φ
  · rfl
  tac_simp [eqParts_eq]
  rcases Internal.eqParts φ with _ | ⟨L₀, R₀⟩
  · rfl
  tac_simp [p1_eq, p2_eq]
  refine (?_ : IRel _ _) Φ []
  refine List.rel_foldr (R := fun (p' : Tree) (p : ℕ) ↦ p' = leaf p)
    (fun p' p hp a' a ha ↦ ?_) (fun Φ₁ is ↦ hk is Γ Φ₁ t u)
    (List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun _ _ ↦ rfl))
  subst hp
  intro Φ₁ is
  tac_simp [nthOf_eq, hE, hEh]
  rcases Internal.eval G E n rs 4096 .weak Γ Φ₁ (Tactics.nthOf L₀ p) with _ | ⟨A', dA, _⟩
  · rfl
  rcases Internal.eval G E n rs 4096 .weak Γ Φ₁ (Tactics.nthOf R₀ p) with _ | ⟨B', dB, _⟩
  · rfl
  rcases Internal.eval G E n [.hyp h] 4096 .weak Γ Φ₁ (Tactics.nthOf L₀ p) with _ | ⟨_, dAh, _⟩
  · rfl
  tac_simp [eqParts_eq]
  rcases Internal.eqParts A' with _ | ⟨F, H⟩
  · rfl
  have hr := ha (Φ₁ ++ [Term.eq A' B', A'] ++ Tactics.instEqs F H (args p))
    (is ++ (List.range (args p).length).map (Φ₁.length + 1 + 1 + ·))
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def] at hr
  tac_simp [p1_eq, p2_eq, hargs, instEqs_eq, append_eq, range_eq, add_leaf, mapT_eq,
    List.map_map, length_instEqs, hr, cutInsts_eq]
  simp only [Option.map_eq_bind, Function.comp_def]
  rfl

/-- The mirror's term with a variable moved to a new, innermost variable. -/
@[simp] theorem subVar_eq (i : ℕ) (x : Term) :
    «Tactics.subVar» (leaf i) (encTerm x) = encTerm (Tactics.subVar i x) := by
  simp only [«Tactics.subVar», weaken1_eq, Tactics.subVar]
  exact subst_eq _ _ (fun j ↦ if j = i + 1 then Term.var 0 else Term.var j) fun j ↦ by
    mirror_simp [beq_iff_eq]
    split <;> rfl

/-- The mirror's proof by case analysis of a list variable that a hypothesis mentions, the
hypothesis reverted, each case by its related prover. -/
theorem revertCase_eq (G : Internal.Globals) (n o lb i h : ℕ)
    (pNil' pCons' : List Tree → List Tree → Tree → Tree → Tree) (pNil pCons : Internal.Prover)
    (hN : PRel pNil' pNil) (hC : PRel pCons' pCons) :
    PRel («Tactics.revertCase» (encGlobals G) (leaf n) (leaf o) (leaf lb) (leaf i)
        (leaf h) pNil' pCons')
      (Tactics.revertCase G n o lb i h pNil pCons) := by
  have hN' : ∀ Γ Φ t u, pNil' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((pNil Γ Φ t u).map encDeriv) := hN
  have hC' : ∀ Γ Φ t u, pCons' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((pCons Γ Φ t u).map encDeriv) := hC
  intro Γ Φ t u
  simp only [«Tactics.revertCase», Tactics.revertCase]
  tac_simp [listPart_eq]
  rcases Γ[i]? with _ | c
  · rfl
  tac_simp [listPart_eq]
  rcases Internal.listPart c with _ | a
  · rfl
  tac_simp []
  rcases Φ[h]? with _ | ψ
  · rfl
  tac_simp [ttL_eq, impL_eq, subVar_eq, snocHyp_eq, lowerHyps_eq]
  rcases Internal.lowerHyps G n Γ (Φ.map Internal.weaken1 ++ [Internal.Logic.tt o]) with _ | Φ'
  · rfl
  tac_simp [instAt_eq, eqParts_eq]
  rcases Internal.eqParts ((Tactics.subVar i (t.eq u)).subst
    (Internal.instVar (Term.arr 0 [a] Term.star))) with _ | ⟨t₀, u₀⟩
  · rfl
  tac_simp [instAt_eq, p1_eq, p2_eq, snocHyp_eq, hN']
  rcases pNil Γ (Φ' ++ [(Tactics.subVar i ψ).subst (Internal.instVar (Term.arr 0 [a] Term.star))])
    t₀ u₀ with _ | d₀
  · rfl
  tac_simp [listConsAt_eq, eqParts_eq]
  rcases Internal.eqParts (Internal.listConsAt 1 a (Tactics.subVar i (t.eq u))) with _ | ⟨tc, uc⟩
  · rfl
  tac_simp [weakenElem_eq, snocHyp_eq, p1_eq, p2_eq, hC', impI_eq, trueI_eq, mLam_eq, add_leaf,
    instAt_eq, listConsAt_eq]
  simp only [Option.map_eq_bind, Function.comp_def]
  rfl

/-- A label's position is a definition's exactly at a definition. -/
theorem labelData_eq_defn (l : Internal.Label) : (labelData l).1 = 11 ↔ ∃ k θ, l = .defn k θ := by
  cases l <;> simp [labelData]

/-- The mirror's rule of β-reduction alone. -/
theorem betaRule_rel : List.Forall₂ RRel «Tactics.betaRule» [.rule .beta] :=
  .cons rfl .nil

/-- The mirror's proof of an equation of an implication and truth by the introduction of the
implication, at a related prover. -/
theorem byImpI_eq (G : Internal.Globals) (E : Array Internal.Entry) (o lb : ℕ)
    (p' : List Tree → List Tree → Tree → Tree → Tree) (p : Internal.Prover) (hp : PRel p' p) :
    PRel («Tactics.byImpI» (encGlobals G) (E.toList.map encEntry) (leaf o) (leaf lb) p')
      (Tactics.byImpI G E o lb p) := by
  have hp' : ∀ Γ Φ t u, p' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p Γ Φ t u).map encDeriv) := hp
  have hE : ∀ Γ Φ t, «Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf 0)
      «Tactics.betaRule» (leaf 4096) (leaf 0) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.eval G E 0 [.rule .beta] 4096 .head Γ Φ t).map encTDB) :=
    eval_eq G E 0 _ _ betaRule_rel 4096 .head
  intro Γ Φ t u
  simp only [Tactics.byImpI]
  rcases ht : Internal.eval G E 0 [.rule .beta] 4096 .head Γ Φ t with _ | ⟨t', dt, _⟩
  · simp only [«Tactics.byImpI», hE, ht]
    rfl
  rcases hu : Internal.eval G E 0 [.rule .beta] 4096 .head Γ Φ u with _ | ⟨u', du, _⟩
  · simp only [«Tactics.byImpI», hE, ht, hu]
    rfl
  obtain ⟨l, ts, rfl⟩ : ∃ l ts, t' = RoseTree.node l ts :=
    ⟨t'.label, t'.children, (RoseTree.node_label_children t').symm⟩
  obtain ⟨l', us, rfl⟩ : ∃ l us, u' = RoseTree.node l us :=
    ⟨u'.label, u'.children, (RoseTree.node_label_children u').symm⟩
  simp only [Option.bind_eq_bind, Option.bind_some, RoseTree.label_node, RoseTree.children_node]
  split
  · rename_i k θ q a k' θ'
    simp only [«Tactics.byImpI», hE, ht, hu]
    mirror_simp [p1_encTDB, p2_encTDB, mIs_eq, labelData, mD_eq, mArg_eq, beq_iff_eq,
      label_encTerm, RoseTree.label_node, Bool.and_eq_true]
    by_cases hk : k = o + 2 ∧ k' = o
    · have hp2 := hp' Γ (Φ ++ [Internal.Logic.tt o, a])
      simp only [List.map_append, List.map_cons, List.map_nil] at hp2
      simp only [hk, and_self, ↓reduceIte]
      tac_simp [eqParts_eq]
      rcases Internal.eqParts q with _ | ⟨l₀, r₀⟩
      · rfl
      tac_simp [p1_eq, p2_eq, ttL_eq, hp2, trueI_eq, impI_eq, Internal.Logic.nd]
      simp only [Option.map_eq_bind, Function.comp_def]
    · simp only [hk, ↓reduceIte, Option.map_none]
      rfl
  · rename_i hne
    simp only [«Tactics.byImpI», hE, ht, hu]
    mirror_simp [p1_encTDB, mIs_eq, label_encTerm, RoseTree.label_node, Bool.and_eq_true,
      beq_iff_eq]
    split
    · rename_i hc
      obtain ⟨⟨h11, h2⟩, h11'⟩ := hc
      obtain ⟨k, θ, rfl⟩ := (labelData_eq_defn l).mp h11
      obtain ⟨k', θ', rfl⟩ := (labelData_eq_defn l').mp h11'
      match ts, h2 with
      | [q, a], _ => exact (hne k θ q a k' θ' rfl rfl rfl).elim
    · rfl

/-- The mirror's proof with the conclusions of implications among the hypotheses, cut in by
modus ponens and used as rewriting rules before those given to a related prover from rules. -/
theorem withImpElim_eq (o lb h : ℕ) (is : List ℕ)
    (k' : List (Tree × (Tree → Tree → List Tree → Tree)) →
      List Tree → List Tree → Tree → Tree → Tree)
    (k : List NormRule → Internal.Prover) (hk : KRel k' k) :
    PRel («Tactics.withImpElim» (leaf o) (leaf lb) (leaf h) (is.map leaf) k')
      (Tactics.withImpElim o lb h is k) := by
  intro Γ Φ t u
  simp only [«Tactics.withImpElim», Tactics.withImpElim, foldr_eq]
  refine (?_ : ARel _ _) Φ [] [] .nil
  refine List.rel_foldr (R := fun (i' : Tree) (i : ℕ) ↦ i' = leaf i)
    (fun i' i hi a' a ha ↦ ?_) (fun Φ₁ ex' ex hex ↦ hk ex' ex hex Γ Φ₁ t u)
    (List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun _ _ ↦ rfl))
  subst hi
  intro Φ₁ ex' ex hex
  tac_simp [eqParts_eq]
  rcases Φ₁[i]? with _ | φ
  · rfl
  tac_simp [eqParts_eq]
  rcases Internal.eqParts φ with _ | ⟨L, R⟩
  · rfl
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, L = RoseTree.node l cs :=
    ⟨L.label, L.children, (RoseTree.node_label_children L).symm⟩
  by_cases hc : (labelData l).1 = 11 ∧ cs.length = 2
  · obtain ⟨h11, h2⟩ := hc
    obtain ⟨k₀, θ, rfl⟩ := (labelData_eq_defn l).mp h11
    match cs, h2 with
    | [q, a], _ =>
      have hr := ha (Φ₁ ++ [q]) _ _ (List.rel_append hex (.cons (hypRule_rel Φ₁.length) .nil))
      simp only [List.map_append, List.map_cons, List.map_nil] at hr
      mirror_simp [p1_eq, p2_eq, mIs_eq, labelData, mD_eq, mArg_eq, beq_iff_eq, Bool.and_eq_true,
        RoseTree.label_node, RoseTree.children_node]
      by_cases hk : k₀ = o + 2
      · tac_simp [hk, appendNR_eq, append_eq, hr, trueI_eq, Internal.Logic.nd, add_leaf,
          ↓reduceIte, Option.bind_assoc]
        simp only [Option.map_eq_bind, Function.comp_def]
        rfl
      · simp only [hk, ↓reduceIte]
        rfl
  · mirror_simp [p1_eq, p2_eq, mIs_eq, Bool.and_eq_true, beq_iff_eq, label_encTerm,
      RoseTree.label_node, RoseTree.children_node, hc]
    split
    · exact absurd ⟨rfl, rfl⟩ hc
    · rfl

/-- The mirror's index of a hypothesis rule's hypothesis, at a related rule. -/
theorem hypIndex_eq (r' : Tree × (Tree → Tree → List Tree → Tree)) (r : NormRule)
    (hr : RRel r' r) :
    «Tactics.hypIndex» r' = encOpt ((Tactics.hypIndex r).map leaf) := by
  cases r with
  | thmAt j θ root m k =>
    obtain ⟨p, -, h1, -⟩ := hr
    simp only [«Tactics.hypIndex», h1]
    rfl
  | _ =>
    change r'.1 = _ at hr
    simp only [«Tactics.hypIndex», hr]
    rfl

/-- The mirror's rewriting of an application's argument backward by a theorem. -/
theorem succPredRw_eq (j : ℕ) (l s : Term) :
    «Tactics.succPredRw» (leaf j) (encTerm l) (encTerm s) =
      encOpt ((Tactics.succPredRw j l s).map encTD) := by
  obtain ⟨lab, cs, rfl⟩ : ∃ l cs, s = RoseTree.node l cs :=
    ⟨s.label, s.children, (RoseTree.node_label_children s).symm⟩
  by_cases hc : (labelData lab).1 = 6 ∧ cs.length = 2
  · obtain rfl := (labelData_eq_app lab).mp hc.1
    match cs, hc.2 with
    | [f, x], _ =>
      have hI := instTerm_eq [] [Term.var 1, Term.var 0] l
      simp only [List.map_cons, List.map_nil] at hI
      simp only [«Tactics.succPredRw», Tactics.succPredRw]
      mirror_simp [mIs_eq, labelData, mArg_eq]
      tac_simp [hI]
      rfl
  · mirror_simp [«Tactics.succPredRw», mIs_eq, Bool.and_eq_true, beq_iff_eq,
      label_encTerm, RoseTree.label_node, RoseTree.children_node, hc]
    simp only [Tactics.succPredRw, RoseTree.label_node, RoseTree.children_node]
    split
    · exact absurd ⟨rfl, rfl⟩ hc
    · rfl

/-- The mirror's proof of an equation of two applications by rewriting their arguments backward
by a theorem, at a related prover. -/
theorem bySuccPred_eq (E : Array Internal.Entry) (j : ℕ)
    (p' : List Tree → List Tree → Tree → Tree → Tree) (p : Internal.Prover) (hp : PRel p' p) :
    PRel («Tactics.bySuccPred» (E.toList.map encEntry) (leaf j) p')
      (Tactics.bySuccPred E j p) := by
  have hp' : ∀ Γ Φ t u, p' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p Γ Φ t u).map encDeriv) := hp
  intro Γ Φ t u
  simp only [«Tactics.bySuccPred», Tactics.bySuccPred]
  tac_simp [Array.getElem?_toList, entryLanguage_eq]
  rcases E[j]? with _ | (b | s)
  · rfl
  · tac_simp [entryLanguage_eq, Internal.Entry.language?, thConcl_eq, eqParts_eq]
    rcases Internal.eqParts b.concl with _ | ⟨l, r⟩
    · rfl
    tac_simp [p1_eq, succPredRw_eq]
    rcases Tactics.succPredRw j l t with _ | ⟨t', dt⟩
    · rfl
    rcases Tactics.succPredRw j l u with _ | ⟨u', du⟩
    · rfl
    tac_simp [p1_encTD, p2_encTD, hp']
    simp only [Option.map_eq_bind, Function.comp_def]
  · rfl

/-! Proof search. -/

/-- The mirror's list of lists without its head. -/
@[simp] theorem tailTss_eq (xs : List (List Tree)) : «Tactics.tailTss» xs = xs.tail := by
  cases xs <;> rfl

/-- The mirror's concatenation of a list of lists. -/
@[simp] theorem concatTss_eq (xs : List (List Tree)) :
    «Tactics.concatTss» xs = xs.flatten := by
  simp only [«Tactics.concatTss», foldr_eq]
  exact xs.rec rfl fun x xs ih ↦ by rw [List.foldr_cons, ih, append_eq, List.flatten_cons]

/-- The mirror's subterms of an encoded term outside binders and folds' starts and steps. -/
theorem openSubterms_eq (t : Term) :
    «Tactics.openSubterms» (encTerm t) = (Tactics.openSubterms t).map encTerm := by
  simp only [«Tactics.openSubterms», Tactics.openSubterms]
  refine para_enc _ _ (fun (v : List Tree) (w : List Term) ↦ v = w.map encTerm)
    «Tactics.subtermsStep» _ (fun l v xs hx ↦ ?_) t
  have hc : ∀ k, ((xs.map fun x ↦ x.2.1).drop k).flatten =
      (((xs.map fun x ↦ (x.1, x.2.2)).drop k).flatMap (·.2)).map encTerm := fun k ↦ by
    rw [← List.map_drop, ← List.map_drop, List.flatMap_map, List.map_flatMap]
    simp only [List.flatten_eq_flatMap, List.flatMap_map]
    exact List.flatMap_congr fun x hx' ↦ hx x (List.mem_of_mem_drop hx')
  have hr : ∀ k : ℕ, Nat.repeat «Tactics.tailTss» (k + 1)
      (v :: xs.map fun x ↦ x.2.1) = (xs.map fun x ↦ x.2.1).drop k :=
    Nat.rec rfl fun k ih ↦ by rw [Nat.repeat, ih, tailTss_eq, List.tail_drop]
  have h0 := hc 0
  simp only [List.drop_zero] at h0
  change «Tactics.subtermsStep» (encTerm (RoseTree.node l (xs.map Prod.fst))) _ = _
  have h2 : Nat.repeat «Tactics.tailTss» 2 (v :: xs.map fun x ↦ x.2.1) =
      (xs.map fun x ↦ x.2.1).drop 1 := hr 1
  have h3 : Nat.repeat «Tactics.tailTss» 3 (v :: xs.map fun x ↦ x.2.1) =
      (xs.map fun x ↦ x.2.1).drop 2 := hr 2
  simp only [«Tactics.subtermsStep»]
  cases l <;> mirror_simp [labelData, label_encTerm, RoseTree.label_node, tailTss_eq,
    concatTss_eq, iter_leaf]
  all_goals first
    | rw [h3, hc 2]
    | rw [h2, hc 1]
    | rw [h0]

/-- The mirror's first image of an element of a list that is present, at a related function. -/
theorem findSomeT_eq {α β : Type} (e : α → Tree) (g : β → Tree) (f' : Tree → Tree)
    (f : α → Option β) (hf : ∀ x, f' (e x) = encOpt ((f x).map g)) (xs : List α) :
    «Tactics.findSomeT» f' (xs.map e) = encOpt ((xs.findSome? f).map g) := by
  simp only [«Tactics.findSomeT», foldr_eq]
  exact xs.rec rfl fun x xs ih ↦ by
    simp only [List.map_cons, List.foldr_cons, ih, hf, List.findSome?_cons]
    cases f x <;> rfl

/-- The mirror's test that an encoded term mentions a variable. -/
@[simp] theorem mentions_eq (t : Term) (i : ℕ) :
    «Tactics.mentions» (encTerm t) (leaf i) = ofBool (Tactics.mentions t i) := by
  simp only [«Tactics.mentions», uses_eq, lt_leaf, Tactics.mentions]

/-- A predicate on variables' indices and the mirror's are related when they agree at every
index. -/
def SkipRel (skip' : Tree → Tree) (skip : ℕ → Bool) : Prop := ∀ i, skip' (leaf i) = ofBool (skip i)

/-- The mirror's index of an encoded term that is a variable a predicate does not hold of. -/
theorem varUnless_eq (skip' : Tree → Tree) (skip : ℕ → Bool) (hs : SkipRel skip' skip)
    (m : Term) :
    «Tactics.varUnless» skip' (encTerm m) =
      encOpt ((Tactics.varUnless skip m).map leaf) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, m = RoseTree.node l cs :=
    ⟨m.label, m.children, (RoseTree.node_label_children m).symm⟩
  cases l <;> mirror_simp [«Tactics.varUnless», Tactics.varUnless, labelData,
    label_encTerm, mD_eq, none_eq]
  rename_i i
  rw [hs i]
  cases skip i <;> rfl

/-- The mirror's variable an encoded case analysis is stuck on. -/
theorem scrutVar_eq (skip' : Tree → Tree) (skip : ℕ → Bool) (hs : SkipRel skip' skip) (u : Term) :
    «Tactics.scrutVar» skip' (encTerm u) =
      encOpt ((Tactics.scrutVar skip u).map leaf) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, u = RoseTree.node l cs :=
    ⟨u.label, u.children, (RoseTree.node_label_children u).symm⟩
  cases l <;> rcases cs with _ | ⟨f, _ | ⟨m, _ | ⟨e, cs⟩⟩⟩ <;>
    mirror_simp [«Tactics.scrutVar», Tactics.scrutVar, labelData, mIs_eq, none_eq,
      beq_iff_eq, Nat.reduceEqDiff]
  obtain ⟨lf, fcs, rfl⟩ : ∃ l cs, f = RoseTree.node l cs :=
    ⟨f.label, f.children, (RoseTree.node_label_children f).symm⟩
  cases lf <;> mirror_simp [labelData, label_encTerm, mD_eq, mArg_eq, none_eq]
  rename_i k θ
  by_cases hk : k = 5
  · subst hk
    mirror_simp [varUnless_eq skip' skip hs]
  · simp only [hk, beq_iff_eq, ↓reduceIte]
    split
    · rename_i h
      exact absurd (Internal.Label.arr.inj h).1 hk
    · rfl

/-- The mirror's variable an encoded fold is stuck on. -/
theorem datumVar_eq (skip' : Tree → Tree) (skip : ℕ → Bool) (hs : SkipRel skip' skip) (u : Term) :
    «Tactics.datumVar» skip' (encTerm u) =
      encOpt ((Tactics.datumVar skip u).map leaf) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, u = RoseTree.node l cs :=
    ⟨u.label, u.children, (RoseTree.node_label_children u).symm⟩
  cases l <;> rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, cs⟩⟩⟩⟩ <;>
    mirror_simp [«Tactics.datumVar», Tactics.datumVar, labelData, mIs_eq, none_eq,
      beq_iff_eq, Nat.reduceEqDiff, mArg_eq, varUnless_eq skip' skip hs]

/-- The mirror's type, test and branches of an encoded conditional of the library. -/
theorem condParts_eq (w : Term) :
    «Tactics.condParts» (encTerm w) = encOpt ((Tactics.condParts w).map encCond) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, w = RoseTree.node l cs :=
    ⟨w.label, w.children, (RoseTree.node_label_children w).symm⟩
  cases l <;> rcases cs with _ | ⟨d, _ | ⟨y, _ | ⟨c, _ | ⟨e, cs⟩⟩⟩⟩ <;>
    mirror_simp [«Tactics.condParts», Tactics.condParts, labelData, mIs_eq, none_eq,
      beq_iff_eq, Nat.reduceEqDiff]
  · rename_i k θ
    rcases θ with _ | ⟨a, _ | ⟨b, θ⟩⟩ <;>
      mirror_simp [mD_eq, mArg_eq, labelData, beq_iff_eq, Nat.reduceEqDiff, some_eq, none_eq,
        «Theory.l4»]
    · by_cases hk : k = 6
      · simp only [hk, ↓reduceIte, Translation.D.cond, Option.map_some, encCond]
        rfl
      · simp only [hk, ↓reduceIte, Translation.D.cond, Option.map_none]
    · split
      · rename_i h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        omega
      · rfl
  · split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      omega
    · rfl

/-- The mirror's variable an encoded folded conditional is stuck on. -/
theorem condVar_eq (skip' : Tree → Tree) (skip : ℕ → Bool) (hs : SkipRel skip' skip) (u : Term) :
    «Tactics.condVar» skip' (encTerm u) = encOpt ((Tactics.condVar skip u).map leaf) := by
  simp only [«Tactics.condVar», Tactics.condVar, condParts_eq, bindO_eq]
  rcases Tactics.condParts u with _ | ⟨a, c, y, d⟩
  · rfl
  · simp only [Option.map_some, Option.elim_some, encCond, children_eq, RoseTree.children_node]
    mirror_simp [varUnless_eq skip' skip hs]

/-- The mirror's variable an encoded weak normal form is stuck on. -/
theorem stuckVar_eq (skip' : Tree → Tree) (skip : ℕ → Bool) (hs : SkipRel skip' skip) (t : Term) :
    «Tactics.stuckVar» skip' (encTerm t) =
      encOpt ((Tactics.stuckVar skip t).map leaf) := by
  simp only [«Tactics.stuckVar», Tactics.stuckVar, openSubterms_eq,
    findSomeT_eq encTerm leaf _ _ (scrutVar_eq skip' skip hs),
    findSomeT_eq encTerm leaf _ _ (datumVar_eq skip' skip hs), isSome_eq]
  cases (Tactics.openSubterms t).findSome? (Tactics.scrutVar skip) <;> rfl

/-- The mirror's variable an encoded weak normal form is stuck on, a folded conditional's test
among them. -/
theorem stuckVarC_eq (skip' : Tree → Tree) (skip : ℕ → Bool) (hs : SkipRel skip' skip)
    (t : Term) :
    «Tactics.stuckVarC» skip' (encTerm t) =
      encOpt ((Tactics.stuckVarC skip t).map leaf) := by
  simp only [«Tactics.stuckVarC», Tactics.stuckVarC, «Tactics.orO»,
    openSubterms_eq, findSomeT_eq encTerm leaf _ _ (condVar_eq skip' skip hs),
    stuckVar_eq skip' skip hs, isSome_eq]
  cases (Tactics.openSubterms t).findSome? (Tactics.condVar skip) <;> rfl

/-- The mirror's conjunction with a true first conjunct. -/
@[simp] theorem and_true_left (x : Tree) : «Prelude.and» (ofBool true) x = x := rfl

/-- The mirror's test of an encoded term's being an application of a definition to two
arguments. -/
theorem isApps2_eq (k : ℕ) (u : Term) :
    «Tactics.isApps2» (leaf k) (encTerm u) = ofBool (Tactics.isApps2 k u) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, u = RoseTree.node l cs :=
    ⟨u.label, u.children, (RoseTree.node_label_children u).symm⟩
  cases l <;> rcases cs with _ | ⟨f, _ | ⟨x, _ | ⟨e, cs⟩⟩⟩ <;>
    mirror_simp [«Tactics.isApps2», Tactics.isApps2, labelData, mIs_eq,
      beq_iff_eq, Nat.reduceEqDiff, and_false_left, and_true_left]
  · obtain ⟨lf, fcs, rfl⟩ : ∃ l cs, f = RoseTree.node l cs :=
      ⟨f.label, f.children, (RoseTree.node_label_children f).symm⟩
    cases lf <;> rcases fcs with _ | ⟨g, _ | ⟨y, _ | ⟨e, fcs⟩⟩⟩ <;>
      mirror_simp [labelData, mIs_eq, mArg_eq, beq_iff_eq, Nat.reduceEqDiff, and_false_left,
        and_true_left]
    · obtain ⟨lg, gcs, rfl⟩ : ∃ l cs, g = RoseTree.node l cs :=
        ⟨g.label, g.children, (RoseTree.node_label_children g).symm⟩
      cases lg <;> mirror_simp [labelData, label_encTerm, mD_eq, beq_iff_eq, and_false_left,
        and_true_left]
      all_goals first
        | rfl
        | (rename_i k' θ
           rcases θ with _ | ⟨a, θ⟩
           · by_cases h : k' = k
             · subst h
               simp
             · simp [h, beq_false_of_ne h]
           · have hn : decide (RoseTree.node 0 (a :: θ) = RoseTree.node 0 ([] : List Tree)) =
                 false := decide_eq_false fun h ↦ by cases h
             simp [hn])
    · rw [beq_false_of_ne (by omega), and_false_left]
  · rw [beq_false_of_ne (by omega), and_false_left]

/-- The mirror's applications of a definition to two arguments among an encoded term's
subterms. -/
theorem appsOf_eq (k : ℕ) (t : Term) :
    «Tactics.appsOf» (leaf k) (encTerm t) = (Tactics.appsOf k t).map encTerm := by
  simp only [«Tactics.appsOf», Tactics.appsOf, openSubterms_eq, foldr_eq]
  exact (Tactics.openSubterms t).rec rfl fun u us ih ↦ by
    simp only [List.map_cons, List.foldr_cons, ih, isApps2_eq, List.filter_cons]
    cases Tactics.isApps2 k u <;> rfl

/-- The removal of duplicates from a list's image under a map, after an accumulator's image,
under a comparison the map preserves. -/
theorem eraseDupsBy_loop_map {α β : Type} (f : α → β) (r : α → α → Bool) (r' : β → β → Bool)
    (hf : ∀ a b, r' (f a) (f b) = r a b) :
    ∀ as bs : List α, List.eraseDupsBy.loop r' (as.map f) (bs.map f) =
      (List.eraseDupsBy.loop r as bs).map f :=
  List.rec (fun bs ↦ by simp only [List.map_nil, List.eraseDupsBy.loop, List.map_reverse])
    fun a as ih bs ↦ by
      have ha : (bs.map f).any (r' (f a)) = bs.any (r a) := by
        simp only [List.any_map, Function.comp_def, hf]
      simp only [List.map_cons, List.eraseDupsBy.loop, ha]
      cases bs.any (r a)
      · exact ih (a :: bs)
      · exact ih bs

/-- The mirror's reversal of an accumulator onto a list by a continuation fold. -/
theorem revOnto_eq (acc : List (List Tree)) : ∀ a : List (List Tree),
    Const.foldr (fun (x : List Tree) (k : List (List Tree) → List (List Tree)) b ↦ k (x :: b))
      (fun b ↦ b) acc a = acc.reverse ++ a :=
  acc.rec (fun _ ↦ rfl) fun x xs ih a ↦ by
    simp only [foldr_eq, List.foldr_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append] at ih ⊢
    exact ih (x :: a)

/-- The mirror's removal of duplicates from a list of lists, the first occurrences kept. -/
theorem eraseDupsTss_loop (xss : List (List Tree)) :
    «Tactics.eraseDupsTss» xss =
      List.eraseDupsBy.loop (fun a b ↦ decide (b = a)) xss [] := by
  have hany (x : List Tree) (acc : List (List Tree)) :
      List.foldr (fun (y : List Tree) (b : Tree) ↦ «Prelude.or»
        («Base.equalTs» y x) b) (leaf 0) acc =
        ofBool (acc.any fun y ↦ decide (y = x)) :=
    acc.rec rfl fun y ys ih ↦ by
      rw [List.foldr_cons, ih, equalTs_eq, or_eq, List.any_cons]
  have h : ∀ acc, Const.foldr (fun (x : List Tree) (k : List (List Tree) → List (List Tree))
      (acc : List (List Tree)) ↦ if (Const.foldr (fun (y : List Tree) (b : Tree) ↦
        «Prelude.or» («Base.equalTs» y x) b) (leaf 0) acc).label ≠ 0
        then k acc else k (x :: acc))
      (fun acc ↦ Const.foldr (fun (x : List Tree) (k : List (List Tree) → List (List Tree)) b ↦
        k (x :: b)) (fun b ↦ b) acc []) xss acc =
      List.eraseDupsBy.loop (fun a b ↦ decide (b = a)) xss acc :=
    xss.rec (fun acc ↦ by simp [List.eraseDupsBy.loop, revOnto_eq]) fun x xs ih acc ↦ by
      simp only [foldr_eq, List.foldr_cons, hany, List.eraseDupsBy.loop] at ih ⊢
      cases acc.any fun y ↦ decide (y = x)
      · exact ih (x :: acc)
      · exact ih acc
  exact h []

/-- The mirror's removal of duplicates from encoded lists of terms. -/
theorem eraseDupsTss_eq (xss : List (List Term)) :
    «Tactics.eraseDupsTss» (xss.map (·.map encTerm)) =
      xss.eraseDups.map (·.map encTerm) := by
  rw [eraseDupsTss_loop, List.eraseDups, List.eraseDupsBy,
    ← eraseDupsBy_loop_map (·.map encTerm) (· == ·) _ ?_ xss []]
  · rfl
  · intro a b
    simp only [List.map_inj_right encTerm_inj, eq_comm]
    exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, decide_eq_true_eq])

/-- The mirror's arguments at which a matching related to a matching of {lit}`k` variables
matches an encoded term's subterms. -/
theorem matchesWith_eq (m' : Tree → Tree → List Tree → Tree)
    (m : ℕ → Term → List (Option Term) → Option (List (Option Term))) (hm : MRel m' m) (k : ℕ)
    (t : Term) :
    «Tactics.matchesWith» m' (leaf k) (encTerm t) =
      (Tactics.matchesWith m k t).map (·.map encTerm) := by
  simp only [«Tactics.matchesWith», Tactics.matchesWith, openSubterms_eq, foldr_eq]
  generalize hσ : (List.range (k + 64)).map (fun j ↦
    if j < k then none else some (Translation.v (j - k))) = σ₀
  have hs : «Base.mapT» (fun j ↦ if (Const.lt j (leaf k)).label ≠ 0 then
      «Prelude.none» else «Prelude.some»
        («Language.mVar» (Const.sub j (leaf k))))
      («Base.range» (Const.add (leaf k) (leaf 64))) = σ₀.map encOT := by
    rw [← hσ]
    simp only [add_leaf, range_eq, mapT_eq, List.map_map]
    refine List.map_congr_left fun j _ ↦ ?_
    by_cases h : j < k <;> simp [h, lt_leaf, sub_leaf, mVar_eq, encOT, none_eq, some_eq]
  have hr (u : Term) : «Base.bindO» (m' (leaf 0) (encTerm u) (σ₀.map encOT))
      (fun s ↦ «Base.allSomeT» («Base.take» (leaf k)
        (Const.children s))) =
      encOpt (((m 0 u σ₀).bind fun σ ↦ (σ.take k).mapM id).map
        fun σ ↦ RoseTree.node 0 (σ.map encTerm)) := by
    rw [hm 0 u σ₀]
    rcases m 0 u σ₀ with _ | σ
    · rfl
    · have hc : Const.children (encSigma σ) = σ.map fun o ↦ encOpt (o.map encTerm) := by
        simp [encSigma, encOT]
      simp only [Option.map_some, bindO_eq, Option.elim_some, hc, take_eq, ← List.map_take,
        allSomeT_eq, Infer.mapM_map_option (fun o : Option Term ↦ o) encTerm,
        Option.bind_some, Option.map_map]
      rfl
  rw [hs, ← eraseDupsTss_eq]
  refine congrArg _ ?_
  exact (Tactics.openSubterms t).rec rfl fun u us ih ↦ by
    simp only [List.map_cons, List.foldr_cons, hr, ih, List.filterMap_cons, isSome_eq]
    rcases m 0 u σ₀ with _ | σ
    · simp
    · cases h : List.mapM (m := Option) id (List.take k σ) <;> simp [h]

/-- The mirror's arguments at which the body of an abstraction of {lit}`k` variables matches an
encoded term's subterms. -/
theorem matchesOf_eq (body : Term) (k : ℕ) (t : Term) :
    «Tactics.matchesOf» (encTerm body) (leaf k) (encTerm t) =
      (Tactics.matchesOf body k t).map (·.map encTerm) :=
  matchesWith_eq _ _ (matchTerm_eq body) k t

/-- The mirror's appending of lists of lists. -/
@[simp] theorem appendTss_eq (xs ys : List (List Tree)) :
    «Tactics.appendTss» xs ys = xs ++ ys := by
  simp only [«Tactics.appendTss», foldr_eq]
  exact xs.rec rfl fun x xs ih ↦ by rw [List.foldr_cons, ih, List.cons_append]

/-- The mirror's arguments at which the body of a hypothesis's abstraction of one variable, in
normal form to a depth, matches the subterms of encoded terms, at related rules. -/
theorem instArgs_eq (m : Internal.Depth) (G : Internal.Globals) (E : Array Internal.Entry)
    (n : ℕ) (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (Γ : List Tree) (Φ : List Term) (t' u' : Term) (h : ℕ) :
    «Tactics.instArgs» (leaf (encDepth m)) (encGlobals G) (E.toList.map encEntry)
        (leaf n) rs' Γ (Φ.map encTerm) (encTerm t') (encTerm u') (leaf h) =
      (Tactics.instArgs m G E n rs Γ Φ t' u' h).map (·.map encTerm) := by
  simp only [«Tactics.instArgs», Tactics.instArgs]
  tac_simp [eqParts_eq]
  rcases Φ[h]? with _ | φ
  · rfl
  tac_simp [eqParts_eq]
  rcases Internal.eqParts φ with _ | ⟨F, H⟩
  · rfl
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, F = RoseTree.node l cs :=
    ⟨F.label, F.children, (RoseTree.node_label_children F).symm⟩
  by_cases hlam : (labelData l).1 = 5 ∧ cs.length = 1
  · obtain ⟨hl, h1⟩ := hlam
    obtain ⟨a, rfl⟩ := (labelData_eq_lam l).mp hl
    match cs, h1 with
    | [b], _ =>
      have he := eval_eq G E n rs' rs hrs 4096 m (a :: Γ) (Φ.map Internal.weaken1) b
      simp only [List.map_map, Function.comp_def] at he
      mirror_simp [p1_eq, mIs_eq, labelData, mArg_eq, mD_eq, mapT_weaken1, he]
      rcases Internal.eval G E n rs 4096 m (a :: Γ) (Φ.map Internal.weaken1) b with _ | ⟨bw, _⟩
      · rfl
      · simp only [Option.map_some, Option.isSome_some, Option.getD_some, p1_encTDB,
          matchesOf_eq, ite_true, appendTss_eq, ← List.map_append, eraseDupsTss_eq]
  · have hf : ((labelData l).1 == 5 && cs.length == 1) = false :=
      Bool.eq_false_iff.mpr fun h ↦ hlam (by simpa only [Bool.and_eq_true, beq_iff_eq] using h)
    mirror_simp [p1_eq, mIs_eq, hf]
    split
    · exact absurd ⟨rfl, rfl⟩ hlam
    · rfl

/-- The mirror's indices with the nonempty lists of arguments found at them. -/
theorem foldr_found (A' : Tree → List (List Tree)) (A : ℕ → List (List Term))
    (hA : ∀ h, A' (leaf h) = (A h).map (·.map encTerm)) (hs : List ℕ) :
    Const.foldr (fun x acc ↦ Const.lcase (A' x) acc fun _ _ ↦ (x, A' x) :: acc) []
        (hs.map leaf) =
      (hs.filterMap fun h ↦ if (A h).isEmpty then none else some (h, A h)).map
        fun p ↦ (leaf p.1, p.2.map (·.map encTerm)) := by
  simp only [foldr_eq, List.foldr_map]
  exact hs.rec rfl fun h hs ih ↦ by
    rw [List.foldr_cons, ih, hA, List.filterMap_cons]
    cases A h <;> rfl

/-- The mirror's continuation fold of proofs with instances found at hypotheses, each cut in
before the rules added so far, at related rules and a related prover from rules to finish. -/
theorem foldr_withInsts_rel (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (m : Internal.Depth)
    (next' : List (Tree × (Tree → Tree → List Tree → Tree)) →
      List Tree → List Tree → Tree → Tree → Tree)
    (next : List NormRule → Internal.Prover) (hn : KRel next' next)
    (found : List (ℕ × List (List Term))) :
    KRel (Const.foldr (fun (ha : Tree × List (List Tree))
        (k : List (Tree × (Tree → Tree → List Tree → Tree)) →
          List Tree → List Tree → Tree → Tree → Tree) extra ↦
        «Tactics.withInsts» (encGlobals G) (E.toList.map encEntry) (leaf n) rs' ha.1
          ha.2 (fun ex ↦ k («Tactics.appendNR» extra ex)) (leaf (encDepth m)))
        next' (found.map fun p ↦ (leaf p.1, p.2.map (·.map encTerm))))
      (found.foldr (fun (p : ℕ × List (List Term)) (k : List NormRule → Internal.Prover) extra ↦
        Tactics.withInsts G E n rs p.1 p.2 (fun ex ↦ k (extra ++ ex)) m) next) := by
  simp only [foldr_eq, List.foldr_map]
  exact found.rec hn fun p found ih ex' ex hex ↦
    withInsts_eq G E n rs' rs hrs p.1 p.2 _ _
      (fun a' a ha ↦ by rw [appendNR_eq]; exact ih _ _ (List.rel_append hex ha)) m

/-- The mirror's proof of an equation by weak reduction with the instances of the hypotheses
below a number at the arguments at which their abstractions' bodies match the sides' normal forms
to a depth, cut in before the rules given to a related prover from rules, at related rules. -/
theorem byInstsOnce_eq (m : Internal.Depth) (G : Internal.Globals) (E : Array Internal.Entry)
    (n : ℕ) (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (hs : ℕ)
    (next' : List (Tree × (Tree → Tree → List Tree → Tree)) →
      List Tree → List Tree → Tree → Tree → Tree)
    (next : List NormRule → Internal.Prover) (hn : KRel next' next) :
    PRel («Tactics.byInstsOnce» (leaf (encDepth m)) (encGlobals G)
        (E.toList.map encEntry) (leaf n) rs' (leaf hs) next')
      (Tactics.byInstsOnce m G E n rs hs next) := by
  have hE : ∀ Γ Φ t, «Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
      (leaf 4096) (leaf (encDepth m)) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.eval G E n rs 4096 m Γ Φ t).map encTDB) :=
    eval_eq G E n rs' rs hrs 4096 m
  intro Γ Φ t u
  simp only [«Tactics.byInstsOnce», Tactics.byInstsOnce, hE]
  rcases Internal.eval G E n rs 4096 m Γ Φ t with _ | ⟨t', dt, _⟩
  · rfl
  tac_simp [hE]
  rcases Internal.eval G E n rs 4096 m Γ Φ u with _ | ⟨u', du, _⟩
  · rfl
  have hmin : (if (Const.lt (leaf hs) (leaf Φ.length)).label ≠ 0 then leaf hs
      else leaf Φ.length) = leaf (min hs Φ.length) := by
    rw [lt_leaf]
    by_cases h : hs < Φ.length
    · rw [decide_eq_true h]
      exact (ite_eq_left (by decide)).trans (congrArg leaf (Nat.min_eq_left (by omega)).symm)
    · rw [decide_eq_false h]
      exact (ite_eq_right (by decide)).trans (congrArg leaf (Nat.min_eq_right (by omega)).symm)
  tac_simp [p1_encTDB, equal_eq, encTerm_eq_iff, hmin, range_eq,
    foldr_found _ _ (instArgs_eq m G E n rs' rs hrs Γ Φ t' u')]
  by_cases htu : t' = u'
  · simp only [htu, decide_true, ofBool_true, label_leaf, ne_eq, one_ne_zero, not_false_eq_true,
      ↓reduceIte]
    exact byMode_eq m G E n rs' rs hrs Γ Φ t u
  simp only [htu, decide_false, ofBool_false, label_leaf, ne_eq, not_true_eq_false, ↓reduceIte]
  generalize (List.range (min hs Φ.length)).filterMap (fun h ↦
    if (Tactics.instArgs m G E n rs Γ Φ t' u' h).isEmpty = true then none
    else some (h, Tactics.instArgs m G E n rs Γ Φ t' u' h)) = found
  rcases found with _ | ⟨p, found⟩
  · rfl
  exact foldr_withInsts_rel G E n rs' rs hrs m next' next hn (p :: found) [] [] .nil Γ Φ t u

/-- The mirror's first present one of two optional trees. -/
@[simp] theorem orO_eq {α : Type} (f : α → Tree) (o o' : Option α) :
    «Tactics.orO» (encOpt (o.map f)) (encOpt (o'.map f)) =
      encOpt ((o.orElse fun _ ↦ o').map f) := by
  cases o <;> rfl

/-- The mirror's proofs, after rules added, by reduction at related rules. -/
theorem instsLast_rel (m : Internal.Depth) (G : Internal.Globals) (E : Array Internal.Entry)
    (n : ℕ) (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) :
    KRel («Tactics.instsLast» (leaf (encDepth m)) (encGlobals G)
        (E.toList.map encEntry) (leaf n) rs')
      (fun extra ↦ Tactics.byMode m G E n (extra ++ rs)) := fun ex' ex hex ↦ by
  simp only [«Tactics.instsLast», appendNR_eq]
  exact byMode_eq m G E n _ _ (List.rel_append hex hrs)

/-- The mirror's round of the instance search, after rules added, at related rules and a
related prover from rules for the next round. -/
theorem instsRound_rel (m : Internal.Depth) (G : Internal.Globals) (E : Array Internal.Entry)
    (n : ℕ) (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (hs : ℕ)
    (next' : List (Tree × (Tree → Tree → List Tree → Tree)) →
      List Tree → List Tree → Tree → Tree → Tree)
    (next : List NormRule → Internal.Prover) (hn : KRel next' next) :
    KRel («Tactics.instsRound» (leaf (encDepth m)) (encGlobals G)
        (E.toList.map encEntry) (leaf n) rs' (leaf hs) next')
      (fun extra Γ Φ t u ↦ (Tactics.byMode m G E n (extra ++ rs) Γ Φ t u).orElse fun _ ↦
        Tactics.byInstsOnce m G E n (extra ++ rs) hs (fun ex ↦ next (extra ++ ex)) Γ Φ t u) := by
  intro ex' ex hex Γ Φ t u
  have hr := List.rel_append hex hrs
  have hI := byInstsOnce_eq m G E n _ _ hr hs (fun a ↦ next' (ex' ++ a)) _
    (fun a' a ha ↦ hn _ _ (List.rel_append hex ha)) Γ Φ t u
  simp only [«Tactics.instsRound», appendNR_eq, byMode_eq m G E n _ _ hr Γ Φ t u]
  rcases Tactics.byMode m G E n (ex ++ rs) Γ Φ t u with _ | d
  · exact hI
  · rfl

/-- The mirror's proof by three rounds of the instance search, at related rules. -/
theorem byInsts_eq (m : Internal.Depth) (G : Internal.Globals) (E : Array Internal.Entry)
    (n : ℕ) (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (hs : ℕ) :
    PRel («Tactics.byInsts» (leaf (encDepth m)) (encGlobals G)
        (E.toList.map encEntry) (leaf n) rs' (leaf hs))
      (Tactics.byInsts m G E n rs hs) :=
  instsRound_rel m G E n rs' rs hrs hs _ _ (instsRound_rel m G E n rs' rs hrs hs _ _
    (instsRound_rel m G E n rs' rs hrs hs _ _ (instsLast_rel m G E n rs' rs hrs))) [] [] .nil

/-- The mirror's test that some encoded hypothesis among the first mentions a variable. -/
theorem mentionsAny_rel (hs : ℕ) (Φ : List Term) :
    SkipRel (fun i ↦ «Base.anyT» (fun x ↦ «Tactics.mentions» x i)
        («Base.take» (leaf hs) (Φ.map encTerm)))
      (fun i ↦ (Φ.take hs).any (Tactics.mentions · i)) := fun i ↦ by
  simp only [take_eq, ← List.map_take, «Base.anyT», foldr_eq, List.foldr_map]
  exact (Φ.take hs).rec rfl fun x xs ih ↦ by
    rw [List.foldr_cons, ih, mentions_eq, or_eq, List.any_cons]

/-- The mirror's iterate of a step of provers from a prover and the recursion of a step of
provers from a prover are related when the starts are and the steps preserve the relation. -/
theorem repeat_rel (step' : (List Tree → List Tree → Tree → Tree → Tree) →
      List Tree → List Tree → Tree → Tree → Tree)
    (step : Internal.Prover → Internal.Prover) (base' : List Tree → List Tree → Tree → Tree → Tree)
    (base : Internal.Prover) (hb : PRel base' base)
    (hs : ∀ r' r, PRel r' r → PRel (step' r') (step r)) (d : ℕ) :
    PRel (Nat.repeat step' d base') (d.rec base fun _ r ↦ step r) :=
  d.rec hb fun _ ih ↦ hs _ _ ih

/-- The mirror's proof by the instance search, or else by case analysis of a variable the sides'
normal forms are stuck on, each case the same way, to a depth, at related rules. -/
theorem byAuto_eq (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (d : ℕ) (m : Internal.Depth) :
    PRel («Tactics.byAuto» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (leaf d) (leaf (encDepth m)))
      (Tactics.byAuto G E n rs d m) := by
  have hE : ∀ Γ Φ t, «Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
      (leaf 4096) (leaf (encDepth m)) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.eval G E n rs 4096 m Γ Φ t).map encTDB) :=
    eval_eq G E n rs' rs hrs 4096 m
  intro Γ₀ Φ₀ t₀ u₀
  simp only [«Tactics.byAuto», Tactics.byAuto, length_eq, List.length_map, iter_leaf]
  refine (?_ : PRel _ _) Γ₀ Φ₀ t₀ u₀
  generalize Φ₀.length = hs
  refine repeat_rel _ _ _ _ (byInsts_eq m G E n rs' rs hrs hs) (fun rec' rec hrec ↦ ?_) d
  have hrec' : ∀ Γ Φ t u, rec' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((rec Γ Φ t u).map encDeriv) := hrec
  intro Γ Φ t u
  simp only [byInsts_eq m G E n rs' rs hrs hs Γ Φ t u]
  rcases Tactics.byInsts m G E n rs hs Γ Φ t u with _ | q
  swap
  · rfl
  have h0 : SkipRel (fun _ ↦ leaf 0) fun _ ↦ false := fun _ ↦ rfl
  have hn : ∀ x, «Tactics.orO» (encOpt none) x = x := fun _ ↦ rfl
  rw [Option.map_none, hn, Option.orElse_none]
  tac_simp [hE]
  rcases Internal.eval G E n rs 4096 m Γ Φ t with _ | ⟨t', dt, _⟩
  · rfl
  tac_simp [hE]
  rcases Internal.eval G E n rs 4096 m Γ Φ u with _ | ⟨u', du, _⟩
  · rfl
  tac_simp [p1_encTDB, stuckVar_eq _ _ (mentionsAny_rel hs Φ), stuckVar_eq _ _ h0, orO_eq]
  generalize ((Tactics.stuckVar (fun i ↦ (Φ.take hs).any (Tactics.mentions · i)) t').orElse
    fun _ ↦ Tactics.stuckVar (fun i ↦ (Φ.take hs).any (Tactics.mentions · i)) u').orElse
    (fun _ ↦ (Tactics.stuckVar (fun _ ↦ false) t').orElse
      fun _ ↦ Tactics.stuckVar (fun _ ↦ false) u') = oi
  rcases oi with _ | i
  · rfl
  tac_simp []
  rcases Γ[i]? with _ | c
  · rfl
  tac_simp [listPart_eq]
  rcases Internal.listPart c with _ | a
  · tac_simp [coprodParts_eq]
    rcases Internal.coprodParts c with _ | p
    · rfl
    · exact bySplit2_eq 3 4 i rec' rec' rec rec hrec hrec Γ Φ t u
  · exact byListSplit_eq G n i rec' rec' rec rec hrec hrec Γ Φ t u

/-! Trees. -/

/-- The mirror's step of the unfolding of trees, the library's. -/
theorem unnodeStep_eq : «Tactics.unnodeStep» = encTerm Tactics.unnodeStep := by
  simp only [«Tactics.unnodeStep», Tactics.unnodeStep,
    GebTests.Prototypes.FreeTopos.Agreement.Translation.lib_eq, nth_eq, List.getElem?_map]
  change _ = encTerm (match Translation.lib[4]? with
    | some d => d.body.children.headD Term.star
    | none => Term.star)
  rcases Translation.lib[4]? with _ | dd
  · rfl
  · simp only [Option.map_some, isSome_eq, Option.isSome_some, ofBool_true, label_leaf, ne_eq,
      one_ne_zero, not_false_eq_true, ↓reduceIte, get_eq, ldBody_eq, mArgs_eq]
    rcases dd.body.children with _ | ⟨x, xs⟩ <;> rfl

/-- The mirror's unfolding of an encoded tree. -/
@[simp] theorem unnodeU_eq (t : Term) :
    «Tactics.unnodeU» (encTerm t) = encTerm (Tactics.unnodeU t) := by
  simp only [«Tactics.unnodeU», unnodeStep_eq, mRoseRec_eq]
  rfl

/-- The mirror's length of a list of functions. -/
@[simp] theorem lenUF_eq (rs : List (Tree → Tree)) :
    «Tactics.lenUF» rs = leaf rs.length := by
  simp only [«Tactics.lenUF», foldr_eq]
  exact rs.rec rfl fun _ _ ih ↦ by rw [List.foldr_cons, ih, add_leaf, List.length_cons]

/-- The mirror's list over a node's children's positions of a child's result at a position and
another tree elsewhere. -/
theorem range_ufAt {β : Type} (e : β → Tree) (xs : List (Term × (Tree → Tree) × (ℕ → β)))
    (hx : ∀ x ∈ xs, ∀ d, x.2.1 (leaf d) = e (x.2.2 d)) (K d : ℕ) (g' : ℕ → Tree)
    (g : Term → β) (hg : ∀ k (h : k < xs.length), g' k = e (g xs[k].1)) :
    (List.range xs.length).map (fun k ↦ if k = K then
        ((xs.map (·.2.1))[k]?.getD fun _ ↦ leaf 0) (leaf d) else g' k) =
      (xs.zipIdx.map fun p ↦ if p.2 = K then p.1.2.2 d else g p.1.1).map e := by
  refine List.ext_getElem (by simp) fun k h₁ h₂ ↦ ?_
  have hk : k < xs.length := by simpa using h₁
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipIdx, zero_add,
    List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]
  split
  · exact hx _ (List.getElem_mem hk) d
  · exact hg k hk

/-- The mirror's list of the children's results at one argument. -/
theorem foldr_ufApply {β : Type} (e : β → Tree) (d : ℕ) :
    ∀ xs : List (Term × (Tree → Tree) × (ℕ → β)),
      (∀ x ∈ xs, ∀ d, x.2.1 (leaf d) = e (x.2.2 d)) →
      List.foldr (fun (r : Tree → Tree) acc ↦ r (leaf d) :: acc) [] (xs.map (·.2.1)) =
        (xs.map (·.2.2 d)).map e :=
  List.rec (fun _ ↦ rfl) fun x xs ih hx ↦ by
    rw [List.map_cons, List.foldr_cons, ih fun y hy ↦ hx y (List.mem_cons_of_mem x hy),
      hx x List.mem_cons_self d]
    rfl

/-- The mirror's rewriting of an encoded term in which a tree rebuilt from the unfolding of a
variable stands for the variable, back to the term. -/
theorem occRewrite_eq (lk i : ℕ) (t : Term) (d : ℕ) :
    «Tactics.occRewrite» (leaf lk) (leaf i) (encTerm t) (leaf d) =
      encDeriv (Tactics.occRewrite lk i t d) := by
  simp only [«Tactics.occRewrite», Tactics.occRewrite]
  refine para_enc _ _ (fun (v : Tree → Tree) (w : ℕ → Deriv) ↦ ∀ d, v (leaf d) = encDeriv (w d))
    («Tactics.occStep» (leaf lk) (leaf i)) _ (fun l v xs hx d ↦ ?_) t d
  change «Tactics.occStep» (leaf lk) (leaf i)
    (encTerm (RoseTree.node l (xs.map Prod.fst))) _ (leaf d) = _
  have hr := range_ufAt encDeriv xs hx
  cases l with
  | var k =>
    mirror_simp [«Tactics.occStep», labelData, mD_eq, label_encTerm]
    by_cases h : k = i + d
    · tac_simp [h, beq_self_eq_true, ↓reduceIte, ite_true]
      rfl
    · tac_simp [h, beq_false_of_ne h, Bool.false_eq_true, ↓reduceIte, ite_false]
  | lam a =>
    mirror_simp [«Tactics.occStep», labelData, label_encTerm, ufTail_eq]
    tac_simp [foldr_ufApply encDeriv (d + 1) xs hx]
  | natRec | listRec =>
    mirror_simp [«Tactics.occStep», labelData, label_encTerm, ufTail_eq, lenUF_eq,
      ufAt_eq, List.getElem?_cons_succ, beq_iff_eq, ← List.getElem?_map]
    rw [hr 2 d (fun _ ↦ «Prover.dNode» (leaf 0) [] []) (fun _ ↦ RoseTree.node .refl [])
      fun _ _ ↦ rfl]
    tac_simp [List.zipIdx_map, List.map_map, Prod.map, id_eq]
  | roseRec c =>
    mirror_simp [«Tactics.occStep», labelData, label_encTerm, ufTail_eq, lenUF_eq,
      ufAt_eq, List.getElem?_cons_succ, beq_iff_eq, ← List.getElem?_map]
    rw [hr 1 d (fun _ ↦ «Prover.dNode» (leaf 0) [] []) (fun _ ↦ RoseTree.node .refl [])
      fun _ _ ↦ rfl]
    tac_simp [List.zipIdx_map, List.map_map, Prod.map, id_eq]
  | _ =>
    mirror_simp [«Tactics.occStep», labelData, label_encTerm, ufTail_eq, mArgs_eq,
      uses_eq, allT_label]
    all_goals
      simp only [Bool.beq_eq_decide_eq, foldr_ufApply encDeriv d xs hx]
      split <;> tac_simp []

/-- The mirror's abstraction, over a new variable of a type, of an encoded term's occurrences of
an encoded term. -/
@[simp] theorem abstractTerm_eq (b : Tree) (x y : Term) :
    «Tactics.abstractTerm» b (encTerm x) (encTerm y) =
      encTerm (Tactics.abstractTerm b x y) := by
  simp only [«Tactics.abstractTerm», Tactics.abstractTerm, weaken1_eq]
  have hgo : ∀ (w : Term) (d : ℕ), Const.para («Tactics.absStep»
      (encTerm (Internal.weaken1 x))) (encTerm w) (leaf d) =
      encTerm (RoseTree.para (fun l cs d ↦
        if RoseTree.node l (cs.map (·.1)) = Term.rename (Internal.weaken1 x) (· + d) then
          Term.var d else
        match l with
        | .lam _ => RoseTree.node l (cs.map fun (_, r) ↦ r (d + 1))
        | .natRec | .listRec => RoseTree.node l (cs.zipIdx.map fun ((c, r), k) ↦
            if k = 2 then r d else c)
        | .roseRec _ => RoseTree.node l (cs.zipIdx.map fun ((c, r), k) ↦
            if k = 1 then r d else c)
        | _ => RoseTree.node l (cs.map fun (_, r) ↦ r d)) w d) := fun w d ↦ by
    refine para_enc _ _ (fun (v : Tree → Tree) (w : ℕ → Term) ↦ ∀ d, v (leaf d) = encTerm (w d))
      («Tactics.absStep» (encTerm (Internal.weaken1 x))) _ (fun l v xs hx d ↦ ?_) w d
    change «Tactics.absStep» (encTerm (Internal.weaken1 x))
      (encTerm (RoseTree.node l (xs.map Prod.fst))) _ (leaf d) = _
    have hr := range_ufAt encTerm xs hx
    have hn : «Language.rename» (encTerm (Internal.weaken1 x))
        (fun j ↦ Const.add j (leaf d)) = encTerm (Term.rename (Internal.weaken1 x) (· + d)) :=
      rename_eq _ _ _ fun _ ↦ rfl
    simp only [«Tactics.absStep», hn, equal_eq, encTerm_eq_iff, List.map_map,
      Function.comp_def]
    by_cases h : RoseTree.node l (xs.map fun x ↦ x.1) = (Internal.weaken1 x).rename (· + d)
    · simp only [h, decide_true, ofBool_true, label_leaf, ne_eq, one_ne_zero, not_false_eq_true,
        ↓reduceIte, mVar_eq]
    simp only [h, decide_false, ofBool_false, label_leaf, ne_eq, not_true_eq_false, ↓reduceIte]
    cases l with
    | lam a =>
      mirror_simp [labelData, label_encTerm, ufTail_eq, encTerm_node,
        foldr_ufApply encTerm (d + 1) xs hx]
    | natRec | listRec =>
      mirror_simp [labelData, label_encTerm, ufTail_eq, lenUF_eq, ufAt_eq,
        List.getElem?_cons_succ, beq_iff_eq, ← List.getElem?_map, encTerm_node,
        «Language.mArgs», tail_eq, List.tail_cons, at_eq]
      rw [hr 2 d (fun k ↦ (xs.map fun x ↦ encTerm x.1).getD k (leaf 0)) id fun k h ↦ by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h,
          Option.map_some, Option.getD_some, id_eq]]
      simp only [List.zipIdx_map, List.map_map, Function.comp_def, Prod.map, id_eq]
    | roseRec c =>
      mirror_simp [labelData, label_encTerm, ufTail_eq, lenUF_eq, ufAt_eq,
        List.getElem?_cons_succ, beq_iff_eq, ← List.getElem?_map, encTerm_node,
        «Language.mArgs», tail_eq, List.tail_cons, at_eq]
      rw [hr 1 d (fun k ↦ (xs.map fun x ↦ encTerm x.1).getD k (leaf 0)) id fun k h ↦ by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h,
          Option.map_some, Option.getD_some, id_eq]]
      simp only [List.zipIdx_map, List.map_map, Function.comp_def, Prod.map, id_eq]
    | _ =>
      mirror_simp [labelData, label_encTerm, ufTail_eq, encTerm_node,
        foldr_ufApply encTerm d xs hx]
  rw [hgo (Internal.weaken1 y) 0, mLam_eq]
  rfl

/-- The mirror's tree constructor at an encoded pair. -/
@[simp] theorem nodeT_eq (p : Term) :
    «Translation.nodeT» (encTerm p) = encTerm (Translation.nodeT p) :=
  mArr_eq 2 [Translation.bitsTy] p

/-- The mirror's type of trees. -/
theorem treeTy_eq : «Translation.treeTy» = Translation.treeTy := rfl

/-- The mirror's type of bitstrings. -/
theorem bitsTy_eq : «Translation.bitsTy» = Translation.bitsTy := rfl

/-- The mirror's type of lists. -/
theorem list_eq (a : Tree) : «Theory.list» a = Geb.FreeTopos.list a := rfl

/-- The mirror's proof by case analysis on a tree variable, by a related prover. -/
theorem byTreeSplit_eq (lk i : ℕ) (p' : List Tree → List Tree → Tree → Tree → Tree)
    (p : Internal.Prover) (hp : PRel p' p) :
    PRel («Tactics.byTreeSplit» (leaf lk) (leaf i) p') (Tactics.byTreeSplit lk i p) := by
  have hp' : ∀ Γ Φ t u, p' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p Γ Φ t u).map encDeriv) := hp
  intro Γ Φ t u
  simp only [«Tactics.byTreeSplit», Tactics.byTreeSplit]
  tac_simp []
  rcases Γ[i]? with _ | c
  · rfl
  by_cases hc : c = Translation.treeTy
  · subst hc
    tac_simp [equal_eq, treeTy_eq, bitsTy_eq, list_eq, abstractVar_eq, nodeT_eq, mPair_eq, hp',
      mLam_eq, mFst_eq, mSnd_eq, unnodeU_eq, occRewrite_eq, decide_true, ofBool_true,
      label_leaf, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, not_true_eq_false]
    rcases p _ _ _ _ with _ | q <;> rfl
  · tac_simp [equal_eq, treeTy_eq, hc, decide_false, ofBool_false, label_leaf, ne_eq,
      not_true_eq_false, not_false_eq_true, ↓reduceIte]

/-- The mirror's proof by case analysis of a variable, a list, a coproduct or a tree, each case
by a related prover. -/
theorem splitStuck_eq (G : Internal.Globals) (n lk i : ℕ)
    (rec' : List Tree → List Tree → Tree → Tree → Tree) (rec : Internal.Prover)
    (hrec : PRel rec' rec) :
    PRel («Tactics.splitStuck» (encGlobals G) (leaf n) (leaf lk) (leaf i) rec')
      (Tactics.splitStuck G n lk i rec) := by
  intro Γ Φ t u
  simp only [«Tactics.splitStuck», Tactics.splitStuck]
  tac_simp []
  rcases Γ[i]? with _ | c
  · rfl
  tac_simp [listPart_eq]
  rcases Internal.listPart c with _ | a
  · tac_simp [coprodParts_eq]
    rcases Internal.coprodParts c with _ | pc
    · by_cases hc : c = Translation.treeTy
      · subst hc
        tac_simp [equal_eq, treeTy_eq, decide_true, ofBool_true, label_leaf, ne_eq, one_ne_zero,
          not_false_eq_true, ↓reduceIte]
        exact byTreeSplit_eq lk i rec' rec hrec Γ Φ t u
      · tac_simp [equal_eq, treeTy_eq, hc, decide_false, ofBool_false, label_leaf, ne_eq,
          not_true_eq_false, ↓reduceIte]
        rfl
    · exact bySplit2_eq 3 4 i rec' rec' rec rec hrec hrec Γ Φ t u
  · exact byListSplit_eq G n i rec' rec' rec rec hrec hrec Γ Φ t u

/-- The mirror's proof by reduction to one normal form, with the instances of the hypotheses where
there are any, or else by case analysis of a variable the normal forms are stuck on, a list, a
coproduct or a tree, each case the same way, to a depth, at related rules. -/
theorem byAutoT_eq (G : Internal.Globals) (E : Array Internal.Entry) (n lk : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (d : ℕ) (m : Internal.Depth) :
    PRel («Tactics.byAutoT» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf lk)
        rs' (leaf d) (leaf (encDepth m)))
      (Tactics.byAutoT G E n lk rs d m) := by
  have hE : ∀ Γ Φ t, «Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
      (leaf 4096) (leaf (encDepth m)) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.eval G E n rs 4096 m Γ Φ t).map encTDB) :=
    eval_eq G E n rs' rs hrs 4096 m
  have h0 : SkipRel (fun _ ↦ leaf 0) fun _ ↦ false := fun _ ↦ rfl
  have hn : ∀ x, «Tactics.orO» (encOpt none) x = x := fun _ ↦ rfl
  intro Γ₀ Φ₀ t₀ u₀
  simp only [«Tactics.byAutoT», Tactics.byAutoT, length_eq, List.length_map, iter_leaf]
  refine (?_ : PRel _ _) Γ₀ Φ₀ t₀ u₀
  generalize Φ₀.length = hs
  have hV : ∀ Γ Φ t u, (if (Const.eq (leaf hs) (leaf 0)).label ≠ 0 then «Prelude.none»
      else «Tactics.byInsts» (leaf (encDepth m)) (encGlobals G)
        (E.toList.map encEntry) (leaf n) rs' (leaf hs) Γ (Φ.map encTerm) (encTerm t)
        (encTerm u)) =
      encOpt ((if hs = 0 then none else Tactics.byInsts m G E n rs hs Γ Φ t u).map encDeriv) := by
    intro Γ Φ t u
    by_cases h : hs = 0
    · subst h
      rfl
    · simp only [eq_leaf, h, beq_false_of_ne h, ofBool_false, label_leaf, ne_eq,
        not_true_eq_false, ↓reduceIte]
      exact byInsts_eq m G E n rs' rs hrs hs Γ Φ t u
  refine repeat_rel _ _ _ _ ?_ (fun rec' rec hrec ↦ ?_) d
  · intro Γ Φ t u
    beta_reduce
    rw [hV]
    tac_simp [hE]
    rcases Internal.eval G E n rs 4096 m Γ Φ t with _ | ⟨t', dt, _⟩
    · exact hn _
    tac_simp [hE]
    rcases Internal.eval G E n rs 4096 m Γ Φ u with _ | ⟨u', du, _⟩
    · exact hn _
    tac_simp [p1_encTDB, p2_encTDB, equal_eq, encTerm_eq_iff]
    by_cases htu : t' = u'
    · simp only [htu, decide_true, ofBool_true, label_leaf, ne_eq, one_ne_zero,
        not_false_eq_true, ↓reduceIte]
      rfl
    · simp only [htu, decide_false, ofBool_false, label_leaf, ne_eq, not_true_eq_false,
        ↓reduceIte]
      exact hn _
  · have hrec' : ∀ Γ Φ t u, rec' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
        encOpt ((rec Γ Φ t u).map encDeriv) := hrec
    intro Γ Φ t u
    beta_reduce
    tac_simp [hE]
    rcases Internal.eval G E n rs 4096 m Γ Φ t with _ | ⟨t', dt, _⟩
    · rfl
    tac_simp [hE]
    rcases Internal.eval G E n rs 4096 m Γ Φ u with _ | ⟨u', du, _⟩
    · rfl
    tac_simp [p1_encTDB, p2_encTDB, equal_eq, encTerm_eq_iff]
    by_cases htu : t' = u'
    · simp only [htu, decide_true, ofBool_true, label_leaf, ne_eq, one_ne_zero,
        not_false_eq_true, ↓reduceIte]
      rfl
    simp only [ne_eq, none_eq] at hV
    simp only [htu, decide_false, ofBool_false, label_leaf, ne_eq, not_true_eq_false,
      ↓reduceIte, hV]
    generalize (if hs = 0 then none else Tactics.byInsts m G E n rs hs Γ Φ t u) = oB
    rcases oB with _ | q
    swap
    · rfl
    rw [Option.map_none, hn, Option.orElse_none]
    tac_simp [stuckVar_eq _ _ (mentionsAny_rel hs Φ), stuckVar_eq _ _ h0, orO_eq]
    generalize ((Tactics.stuckVar (fun i ↦ (Φ.take hs).any (Tactics.mentions · i)) t').orElse
      fun _ ↦ Tactics.stuckVar (fun i ↦ (Φ.take hs).any (Tactics.mentions · i)) u').orElse
      (fun _ ↦ (Tactics.stuckVar (fun _ ↦ false) t').orElse
        fun _ ↦ Tactics.stuckVar (fun _ ↦ false) u') = oi
    rcases oi with _ | i
    · rfl
    exact splitStuck_eq G n lk i rec' rec hrec Γ Φ t u

/-- The mirror's proof by reduction to one weak normal form, or else by case analysis of a
variable the normal forms are stuck on, a folded conditional's test among them, each case the
same way, to a depth, at related rules. -/
theorem byAutoC_eq (G : Internal.Globals) (E : Array Internal.Entry) (n lk : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (d : ℕ) :
    PRel («Tactics.byAutoC» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf lk)
        rs' (leaf d))
      (Tactics.byAutoC G E n lk rs d) := by
  have hE : ∀ Γ Φ t, «Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
      (leaf 4096) (leaf 1) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.eval G E n rs 4096 .weak Γ Φ t).map encTDB) :=
    eval_eq G E n rs' rs hrs 4096 .weak
  have h0 : SkipRel (fun _ ↦ leaf 0) fun _ ↦ false := fun _ ↦ rfl
  have hn : ∀ x, «Tactics.orO» (encOpt none) x = x := fun _ ↦ rfl
  simp only [«Tactics.byAutoC», Tactics.byAutoC, iter_leaf]
  refine repeat_rel _ _ _ _ (byWeak_eq G E n rs' rs hrs) (fun rec' rec hrec ↦ ?_) d
  intro Γ Φ t u
  beta_reduce
  rw [byWeak_eq G E n rs' rs hrs Γ Φ t u]
  rcases Tactics.byWeak G E n rs Γ Φ t u with _ | q
  swap
  · rfl
  rw [Option.map_none, hn, Option.orElse_none]
  tac_simp [hE]
  rcases Internal.eval G E n rs 4096 .weak Γ Φ t with _ | ⟨t', dt, _⟩
  · rfl
  tac_simp [hE]
  rcases Internal.eval G E n rs 4096 .weak Γ Φ u with _ | ⟨u', du, _⟩
  · rfl
  tac_simp [p1_encTDB, stuckVarC_eq _ _ h0, orO_eq]
  generalize (Tactics.stuckVarC (fun _ ↦ false) t').orElse
    (fun _ ↦ Tactics.stuckVarC (fun _ ↦ false) u') = oi
  rcases oi with _ | i
  · rfl
  exact splitStuck_eq G n lk i rec' rec hrec Γ Φ t u

/-- The mirror's proof that a conditional is the conditional with a term's occurrences rewritten
in its first branch, by absorption and a derivation of the rewriting under the mask. -/
@[simp] theorem maskRwD_eq (a b : Tree) (ab : ℕ) (dM : Deriv) (c d x x' z y : Term) :
    «Tactics.maskRwD» a b (leaf ab) (encDeriv dM) (encTerm c) (encTerm d) (encTerm x)
        (encTerm x') (encTerm z) (encTerm y) =
      encDeriv (Tactics.maskRwD a b ab dM c d x x' z y) := by
  simp only [«Tactics.maskRwD», Tactics.maskRwD]
  tac_simp [abstractTerm_eq, GebTests.Prototypes.FreeTopos.Agreement.Translation.condT_eq,
    «Theory.l5»]
  rfl

/-- The mirror's proof that a conditional is the conditional with a term's occurrences rewritten
in its first branch, by a masked lemma. -/
@[simp] theorem maskRw_eq (a b : Tree) (ab j : ℕ) (θ : List Tree) (σ : List Term)
    (c d x x' z y : Term) :
    «Tactics.maskRw» a b (leaf ab) (leaf j) θ (σ.map encTerm) (encTerm c) (encTerm d)
        (encTerm x) (encTerm x') (encTerm z) (encTerm y) =
      encDeriv (Tactics.maskRw a b ab j θ σ c d x x' z y) := by
  simp only [«Tactics.maskRw», Tactics.maskRw, ← maskRwD_eq]
  tac_simp []
  rfl

/-- A rewriting under a mask: the subterm, its rewriting and the derivation of their equation. -/
def encMask (p : Term × Term × Deriv) : Tree :=
  RoseTree.node 0 [encTerm p.1, encTerm p.2.1, encDeriv p.2.2]

/-- The mirror's rewriting of a conditional subterm by a hypothesis under its mask. -/
theorem maskAt_eq (ab cs : ℕ) (Φ : List Term) (a : Tree) (c y d S : Term) (i : ℕ) :
    «Tactics.maskAt» (leaf ab) (leaf cs) (Φ.map encTerm) a (encTerm c) (encTerm y)
        (encTerm d) (encTerm S) (leaf i) =
      encOpt ((Tactics.maskAt ab cs Φ a c y d S i).map encMask) := by
  simp only [«Tactics.maskAt», Tactics.maskAt]
  tac_simp [eqParts_eq]
  rcases Φ[i]? with _ | φ
  · rfl
  tac_simp [eqParts_eq]
  rcases Internal.eqParts φ with _ | ⟨L, R⟩
  · rfl
  tac_simp [p1_eq, p2_eq, condParts_eq]
  rcases Tactics.condParts L with _ | ⟨b, c', x, z⟩
  · rfl
  tac_simp [encCond, at_eq, equal_eq, encTerm_eq_iff, not_eq, List.getD_cons_succ,
    List.getD_cons_zero]
  by_cases hc : c' = c
  swap
  · simp only [hc, decide_false, Bool.not_false, ofBool_true, label_leaf, ne_eq, one_ne_zero,
      not_false_eq_true, ↓reduceIte]
    rfl
  subst hc
  simp only [decide_true, Bool.not_true, ofBool_false, label_leaf, ne_eq, not_true_eq_false,
    ↓reduceIte]
  rcases Tactics.condParts R with _ | ⟨b₂, c'', x', z'⟩
  · by_cases hR : R = z
    swap
    · simp only [Option.map_none, isSome_eq, Option.isSome_none, ofBool_false, label_leaf,
        not_true_eq_false, ↓reduceIte, hR, decide_false, bindO_eq, Option.elim_none]
    subst hR
    simp only [Option.map_none, isSome_eq, Option.isSome_none, ofBool_false, ofBool_true,
      label_leaf, not_true_eq_false, ↓reduceIte, decide_true, one_ne_zero, not_false_eq_true,
      bindO_eq, Option.elim_some, pr_eq, p1_eq, p2_eq, encTerm_eq_iff, abstractTerm_eq, mArgs_eq]
    by_cases hx : x = R
    · simp only [hx, decide_true, ofBool_true, label_leaf, one_ne_zero, not_false_eq_true,
        ↓reduceIte]
      rfl
    simp only [hx, decide_false, ofBool_false, label_leaf, not_true_eq_false, ↓reduceIte]
    rcases (Tactics.abstractTerm b x y).children with _ | ⟨h, rest⟩
    · rfl
    mirror_simp [uses_eq, List.head?_cons, Option.bind_some, beq_iff_eq]
    by_cases hu : Internal.uses h 0 = 0
    · simp only [hu, ↓reduceIte]
      rfl
    simp only [hu, ↓reduceIte, Option.map_some, encMask, ← maskRwD_eq, subst_instVar,
      GebTests.Prototypes.FreeTopos.Agreement.Translation.condT_eq]
    tac_simp []
    rfl
  · simp only [Option.map_some, isSome_eq, Option.isSome_some, ofBool_true, label_leaf,
      one_ne_zero, not_false_eq_true, ↓reduceIte, get_eq, encCond, RoseTree.children_node,
      List.getD_cons_succ, List.getD_cons_zero, encTerm_eq_iff, and_eq, ← Bool.decide_and]
    by_cases h2 : c'' = c' ∧ z' = z
    swap
    · simp only [h2, decide_false, ofBool_false, label_leaf, not_true_eq_false, ↓reduceIte,
        bindO_eq, Option.elim_none]
      rfl
    simp only [h2, decide_true, and_self, ofBool_true, label_leaf, one_ne_zero,
      not_false_eq_true, ↓reduceIte, bindO_eq, Option.elim_some, pr_eq, p1_eq, p2_eq,
      encTerm_eq_iff, abstractTerm_eq, mArgs_eq]
    by_cases hx : x = x'
    · simp only [hx, decide_true, ofBool_true, label_leaf, one_ne_zero, not_false_eq_true,
        ↓reduceIte]
      rfl
    simp only [hx, decide_false, ofBool_false, label_leaf, not_true_eq_false, ↓reduceIte]
    rcases (Tactics.abstractTerm b x y).children with _ | ⟨h, rest⟩
    · rfl
    mirror_simp [uses_eq, List.head?_cons, Option.bind_some, beq_iff_eq]
    by_cases hu : Internal.uses h 0 = 0
    · simp only [hu, ↓reduceIte]
      rfl
    simp only [hu, ↓reduceIte, Option.map_some, encMask, ← maskRwD_eq, subst_instVar,
      GebTests.Prototypes.FreeTopos.Agreement.Translation.condT_eq]
    tac_simp []
    rfl

/-- The mirror's rewriting of the first conditional subterm of an encoded term by a hypothesis
under its mask, the latest hypothesis first. -/
theorem maskSub_eq (ab cs : ℕ) (Φ : List Term) (w : Term) :
    «Tactics.maskSub» (leaf ab) (leaf cs) (Φ.map encTerm) (encTerm w) =
      encOpt ((Tactics.maskSub ab cs Φ w).map encMask) := by
  simp only [«Tactics.maskSub», Tactics.maskSub, openSubterms_eq]
  refine findSomeT_eq encTerm encMask _ _ (fun S ↦ ?_) _
  simp only [condParts_eq, bindO_eq]
  rcases Tactics.condParts S with _ | ⟨a, c, y, d⟩
  · rfl
  simp only [Option.map_some, Option.elim_some, Option.bind_eq_bind, Option.bind_some, encCond,
    at_eq, length_eq, List.length_map, range_eq, reverse_eq, ← List.map_reverse]
  exact findSomeT_eq leaf encMask _ _ (maskAt_eq ab cs Φ a c y d S) _

/-- The mirror's provers from added rules and provers from rules, and provers from added rules
and provers from rules, are related when they are related provers at related added rules and
related provers from rules. -/
def MSRel (ms' : List (Tree × (Tree → Tree → List Tree → Tree)) →
      (List (Tree × (Tree → Tree → List Tree → Tree)) →
        List Tree → List Tree → Tree → Tree → Tree) →
      List Tree → List Tree → Tree → Tree → Tree)
    (ms : List NormRule → (List NormRule → Internal.Prover) → Internal.Prover) : Prop :=
  ∀ ex' ex, List.Forall₂ RRel ex' ex → ∀ p' p, KRel p' p → PRel (ms' ex' p') (ms ex p)

/-- The mirror's iterate of a step of provers from added rules and provers from rules, and the
recursion of such a step, are related when the starts are and the steps preserve the relation. -/
theorem repeat_msRel
    (step' : (List (Tree × (Tree → Tree → List Tree → Tree)) →
        (List (Tree × (Tree → Tree → List Tree → Tree)) →
          List Tree → List Tree → Tree → Tree → Tree) →
        List Tree → List Tree → Tree → Tree → Tree) →
      List (Tree × (Tree → Tree → List Tree → Tree)) →
        (List (Tree × (Tree → Tree → List Tree → Tree)) →
          List Tree → List Tree → Tree → Tree → Tree) →
        List Tree → List Tree → Tree → Tree → Tree)
    (step : (List NormRule → (List NormRule → Internal.Prover) → Internal.Prover) →
      List NormRule → (List NormRule → Internal.Prover) → Internal.Prover)
    (base' : List (Tree × (Tree → Tree → List Tree → Tree)) →
        (List (Tree × (Tree → Tree → List Tree → Tree)) →
          List Tree → List Tree → Tree → Tree → Tree) →
        List Tree → List Tree → Tree → Tree → Tree)
    (base : List NormRule → (List NormRule → Internal.Prover) → Internal.Prover)
    (hb : MSRel base' base) (hs : ∀ r' r, MSRel r' r → MSRel (step' r') (step r)) (n : ℕ) :
    MSRel (Nat.repeat step' n base') (n.rec base fun _ r ↦ step r) :=
  n.rec hb fun _ ih ↦ hs _ _ ih

/-- The mirror's proof by rewriting under masks by the hypotheses up to a number of times, and
then by a related prover from rules with the rules added, at related rules. -/
theorem byMaskSubs_eq (G : Internal.Globals) (E : Array Internal.Entry) (ab cs : ℕ)
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (n : ℕ)
    (p' : List (Tree × (Tree → Tree → List Tree → Tree)) →
      List Tree → List Tree → Tree → Tree → Tree)
    (p : List NormRule → Internal.Prover) (hp : KRel p' p) :
    PRel («Tactics.byMaskSubs» (encGlobals G) (E.toList.map encEntry) (leaf ab)
        (leaf cs) rs' (leaf n) p')
      (Tactics.byMaskSubs G E ab cs rs n p) := by
  simp only [«Tactics.byMaskSubs», Tactics.byMaskSubs, iter_leaf]
  refine repeat_msRel _ _ _ _ (fun ex' ex hex p' p hp ↦ hp ex' ex hex)
    (fun rec' rec hrec ↦ ?_) n [] [] .nil p' p hp
  intro ex' ex hex p' p hp
  beta_reduce
  simp only [appendNR_eq]
  refine byNF_eq G E 0 _ _ (List.rel_append hex hrs) .weak _ _ fun Γ Φ t u ↦ ?_
  have hp' : ∀ Γ Φ t u, p' ex' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p ex Γ Φ t u).map encDeriv) := hp ex' ex hex
  simp only [maskSub_eq, orO_eq]
  generalize (Tactics.maskSub ab cs Φ t).orElse (fun _ ↦ Tactics.maskSub ab cs Φ u) = oS
  rcases oS with _ | ⟨S, S', dS⟩
  · exact hp' Γ Φ t u
  have hr := hrec _ _ (.cons (hypRule_rel Φ.length) hex) p' p hp Γ (Φ ++ [Term.eq S S']) t u
  simp only [List.map_append, List.map_cons, List.map_nil] at hr
  tac_simp [encMask, isSome_eq, Option.isSome_some, ofBool_true, label_leaf, one_ne_zero,
    not_false_eq_true, ↓reduceIte, get_eq, at_eq, List.getD_cons_succ, List.getD_cons_zero,
    append_eq, hr]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte]
  rcases rec (NormRule.hyp Φ.length :: ex) p Γ (Φ ++ [S.eq S']) t u with _ | q <;> rfl

/-- The mirror's proof by generalizing an encoded term of a type, by a related prover at a new,
innermost variable. -/
theorem byGeneralize_eq (a : Tree) (c : Term) (p' : List Tree → List Tree → Tree → Tree → Tree)
    (p : Internal.Prover) (hp : PRel p' p) :
    PRel («Tactics.byGeneralize» a (encTerm c) p') (Tactics.byGeneralize a c p) := by
  have hp' : ∀ Γ Φ t u, p' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p Γ Φ t u).map encDeriv) := hp
  intro Γ Φ t u
  simp only [«Tactics.byGeneralize», Tactics.byGeneralize]
  tac_simp [abstractTerm_eq, hp', applyAbs_eq]
  rcases p (a :: Γ) (Φ.map Internal.weaken1) _ _ with _ | q <;> rfl

end GebTests.Prototypes.FreeTopos.Agreement.Tactics

end
