/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Derivation
public import Geb.Prototypes.FreeTopos.Internal.Prove

set_option doc.verso true in
/-!
# The prover written in Geb

The functions of {lit}`bootstrap/free-topos/prove.geb`, in the Lean the bootstrap compiler emits
({lit}`GebMirror.Metalogic`), agree with the Lean prover of the internal language
({name}`Geb.FreeTopos.Internal.normalize`) at every encoded input: the matching of patterns, the
rewriting at a term's root by the normalizer's rules, normalization innermost first, the
reduction to a depth, and the proofs of an equation, so that the prover written in Geb
constructs exactly the derivations the Lean prover constructs.

## Main definitions

* {lit}`encDB`, {lit}`encTDB`, {lit}`encOT`, {lit}`encDepth` — a rewriting's derivation with
  its mark, a term with it, an optional term of an assignment, and a depth of reduction.
* {lit}`MRel`, {lit}`RRel`, {lit}`NRel`, {lit}`ERel`, {lit}`PRel` — the relations of the
  mirror's matchings, rules, normalizations, reductions to a depth and provers to the prover's.

## Main statements

* {lit}`byNorm_eq`, {lit}`byNormW_eq` — the proofs by normalization, innermost first and through
  weak head normal forms, agree.
* {lit}`byNatInd_eq`, {lit}`byListInd_eq`, {lit}`byNatIndHyp_eq`, {lit}`byListIndHyp_eq`,
  {lit}`byRoseInd_eq` — the proofs by induction, each premise by normalization, agree.
* {lit}`byFunExt_eq`, {lit}`bySplit_eq`, {lit}`byListIndWith_eq`, {lit}`byRoseIndHyp_eq` — the
  proofs of an equation from proofs of others agree at related provers.

## Tags

prover, internal language, normalization, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Prove

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Fold GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.Language
  GebTests.Prototypes.FreeTopos.Agreement.Derivation
open Internal (Term Deriv NormRule)
open scoped FinEnum

/-- The mirror's bindings and images of optional values are the base's of optional trees. -/
@[template] theorem bindP_def : «Prover.bindP» = «Base.bindO» := rfl

@[template, inherit_doc bindP_def] theorem bindAA_def : «Prover.bindAA» = «Base.bindO» := rfl

@[template, inherit_doc bindP_def] theorem bindAP_def : «Prover.bindAP» = «Base.bindO» := rfl

@[template, inherit_doc bindP_def] theorem bindHP_def : «Prover.bindHP» = «Base.bindO» := rfl

@[template, inherit_doc bindP_def] theorem bindNT_def : «Prover.bindNT» = «Base.bindO» := rfl

@[template, inherit_doc bindP_def] theorem bindNN_def : «Prover.bindNN» = «Base.bindO» := rfl

@[template, inherit_doc bindP_def] theorem bindTN_def : «Prover.bindTN» = «Base.bindO» := rfl

@[template, inherit_doc bindP_def] theorem bindSN_def : «Prover.bindSN» = «Base.bindO» := rfl

@[template, inherit_doc bindP_def] theorem bindLN_def : «Prover.bindLN» = «Base.bindO» := rfl

@[template, inherit_doc bindP_def] theorem bindHT_def : «Prover.bindHT» = «Base.bindO» := rfl

@[template, inherit_doc bindP_def] theorem mapTP_def : «Prover.mapTP» = «Base.mapO» := rfl

@[template, inherit_doc bindP_def] theorem mapNN_def : «Prover.mapNN» = «Base.mapO» := rfl

/-- The mirror's optional list of present normal forms is the base's optional trees. -/
@[template] theorem allSomeN_def : «Prover.allSomeN» = «Base.allSomeT» := by
  funext ms
  simp only [«Prover.allSomeN», template, «Prover.nfrs»]
  exact allJust_allSomeT ms

/-- The mirror's marked derivations, normal forms and scoped terms are pairs of trees, with the
pairs' components. -/
@[template] theorem mark_def : «Prover.mark» = «Language.pr» := rfl

@[template, inherit_doc mark_def] theorem mDeriv_def : «Prover.mDeriv» = «Language.p1» := rfl

@[template, inherit_doc mark_def] theorem mFlag_def : «Prover.mFlag» = «Language.p2» := rfl

@[template, inherit_doc mark_def] theorem nfr_def : «Prover.nfr» = «Language.pr» := rfl

@[template, inherit_doc mark_def] theorem nfTerm_def : «Prover.nfTerm» = «Language.p1» := rfl

@[template, inherit_doc mark_def] theorem nfMarked_def : «Prover.nfMarked» = «Language.p2» := rfl

@[template, inherit_doc mark_def] theorem scopeTerm_def : «Prover.scopeTerm» = «Language.pr» :=
  rfl

@[template, inherit_doc mark_def] theorem scopeOf_def : «Prover.scopeOf» = «Language.p1» := rfl

@[template, inherit_doc mark_def] theorem termOf_def : «Prover.termOf» = «Language.p2» := rfl

/-- The mirror's rules of the normalizer that the prover builds, as their encodings. -/
@[template] theorem nrThmAt_def :
    «Prover.nrThmAt» = fun j th p k ↦ RoseTree.node 5 [j, th, p, k] := rfl

@[template, inherit_doc nrThmAt_def] theorem nrHyp_def :
    «Prover.nrHyp» = fun i ↦ RoseTree.node 6 [i] := rfl

/-- The mirror's lists of the elements of a node. -/
@[template] theorem assigned_def : «Prover.assigned» = Const.children := rfl

@[template, inherit_doc assigned_def] theorem termsOf_def : «Prover.termsOf» = Const.children :=
  rfl

@[template, inherit_doc assigned_def] theorem objsOf_def : «Prover.objsOf» = Const.children := rfl

@[template, inherit_doc assigned_def] theorem nfrsOf_def : «Prover.nfrsOf» = Const.children := rfl

/-- The mirror's lists wrapped as datatypes, each the node of label zero over its elements. -/
@[simp, template] theorem assign_wrap (xs : List Tree) :
    «Prover.assign» xs = RoseTree.node 0 xs := rfl

@[simp, template, inherit_doc assign_wrap] theorem nfrs_wrap (xs : List Tree) :
    «Prover.nfrs» xs = RoseTree.node 0 xs := rfl

/-- A rewriting's derivation with its mark, as the node of the two. -/
def encDB (p : Deriv × Bool) : Tree := encPair (encDeriv p.1, ofBool p.2)

/-- A term with its rewriting's derivation and mark. -/
def encTDB (p : Term × Deriv × Bool) : Tree := encPair (encTerm p.1, encDB p.2)

/-- A term with a derivation. -/
def encTD (p : Term × Deriv) : Tree := encPair (encTerm p.1, encDeriv p.2)

/-- An optional term of an assignment of a pattern's variables. -/
def encOT (o : Option Term) : Tree := encOpt (o.map encTerm)

/-- An assignment of a pattern's variables, as the node of its optional terms. -/
def encSigma (σ : List (Option Term)) : Tree := RoseTree.node 0 (σ.map encOT)

/-- The derivation of an encoded rewriting. -/
@[simp] theorem p1_encDB (p : Deriv × Bool) : «Language.p1» (encDB p) = encDeriv p.1 :=
  rfl

/-- The mark of an encoded rewriting. -/
@[simp] theorem p2_encDB (p : Deriv × Bool) : «Language.p2» (encDB p) = ofBool p.2 :=
  rfl

/-- The term of an encoded reduction. -/
@[simp] theorem p1_encTDB (p : Term × Deriv × Bool) :
    «Language.p1» (encTDB p) = encTerm p.1 :=
  rfl

/-- The rewriting of an encoded reduction. -/
@[simp] theorem p2_encTDB (p : Term × Deriv × Bool) :
    «Language.p2» (encTDB p) = encDB p.2 :=
  rfl

/-- The term of an encoded rewriting at the root. -/
@[simp] theorem p1_encTD (p : Term × Deriv) : «Language.p1» (encTD p) = encTerm p.1 :=
  rfl

/-- The derivation of an encoded rewriting at the root. -/
@[simp] theorem p2_encTD (p : Term × Deriv) : «Language.p2» (encTD p) = encDeriv p.2 :=
  rfl

/-- The mirror's matching of a pattern and a matching are related when they agree at every
depth, encoded term and encoded assignment. -/
def MRel (m' : Tree → Tree → List Tree → Tree)
    (m : ℕ → Term → List (Option Term) → Option (List (Option Term))) : Prop :=
  ∀ d t σ, m' (leaf d) (encTerm t) (σ.map encOT) = encOpt ((m d t σ).map encSigma)

/-- The mirror's rule, with its matching, and a rule of the normalizer are related: a prepared
theorem's node holds a pattern of its root's label and a related matching, and any other rule is
its encoding. -/
def RRel (r' : Tree × (Tree → Tree → List Tree → Tree)) : NormRule → Prop
  | .thmAt j θ root m k => ∃ p : Term, p.label = root ∧
      r'.1 = RoseTree.node 5 [leaf j, RoseTree.node 0 θ, encTerm p, leaf k] ∧ MRel r'.2 m
  | r => r'.1 = encRule r

/-! Derivations. -/

/-- The mirror's derivation of a rule's position and data over encoded premises. -/
@[simp] theorem dNode_eq (r : Internal.Rule) (cs : List Deriv) :
    «Prover.dNode» (leaf (ruleData r).1) (ruleData r).2 (cs.map encDeriv) =
      encDeriv (RoseTree.node r cs) := by
  simp [«Prover.dNode», «Language.mNode», encDeriv]

/-- The mirror's identity derivation. -/
@[simp] theorem dRefl_eq : «Prover.dRefl» = encDB Internal.dRefl := rfl

/-- The mirror's derivation of one rewriting after another. -/
@[simp] theorem dTrans_eq (a b : Deriv × Bool) :
    «Prover.dTrans» (encDB a) (encDB b) = encDB (Internal.dTrans a b) := by
  rcases a with ⟨a, _ | _⟩ <;> rcases b with ⟨b, _ | _⟩ <;> rfl

/-- The mirror's derivation of a node's rewriting from its children's. -/
@[simp] theorem dCong_eq (cs : List (Deriv × Bool)) :
    «Prover.dCong» (cs.map encDB) = encDB (Internal.dCong cs) := by
  have ha : ∀ cs : List (Deriv × Bool),
      «Base.anyT» «Language.p2» (cs.map encDB) = ofBool (cs.any (·.2)) :=
    List.rec rfl fun c cs ih ↦ by
      simp only [«Base.anyT», foldr_eq, List.map_cons, List.foldr_cons,
        List.any_cons] at ih ⊢
      rw [ih]
      rcases c with ⟨d, _ | _⟩ <;> rfl
  have hm : cs.map (fun c ↦ «Language.p1» (encDB c)) = (cs.map Prod.fst).map encDeriv := by
    simp [encDB, List.map_map, Function.comp_def]
  simp only [«Prover.dCong», template, ha, Internal.dCong, mapT_eq, List.map_map,
    Function.comp_def, hm]
  cases cs.any (·.2)
  · rfl
  · have h := dNode_eq .cong (cs.map Prod.fst)
    simp only [List.map_map, Function.comp_def] at h
    simp [ofBool, encDB, ← h]
    rfl

/-- The mirror's test whether a pattern's root may match a term's root. -/
@[simp] theorem sameShape_eq (p t : Term) :
    «Prover.sameShape» (encTerm p) (encTerm t) =
      ofBool (Internal.sameShape p.label t.label) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
    ⟨p.label, p.children, (RoseTree.node_label_children p).symm⟩
  obtain ⟨l', cs', rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
    ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩
  simp only [«Prover.sameShape», template, encTerm_node]
  cases l <;> cases l' <;> mirror_simp [labelData, Internal.sameShape] <;> rfl

/-- The mirror's list with an element replaced. -/
@[simp] theorem setAt_eq (xs : List Tree) (i : ℕ) (x : Tree) :
    «Prover.setAt» xs (leaf i) x = xs.set i x := by
  simp only [«Prover.setAt», template, length_eq, range_eq, mapT_eq, List.map_map,
    Function.comp_def, eq_leaf, at_eq]
  refine List.ext_getElem (by simp) fun k h₁ h₂ ↦ ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_set]
  by_cases h : i = k
  · simp [h]
  · have h' : k ≠ i := fun e ↦ h e.symm
    simp [h, h', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₂)]

/-! The matching of patterns. -/

/-- The mirror's lowering of an encoded term past {lit}`d` binders, the term itself under none. -/
theorem lowerBy_eq (d : ℕ) (t : Term) :
    (if (Const.eq (leaf d) (leaf 0)).label ≠ 0 then encTerm t
      else «Language.rename» (encTerm t) fun j ↦ Const.sub j (leaf d)) =
      encTerm (if d = 0 then t else Internal.Term.rename t (· - d)) := by
  by_cases h : d = 0
  · simp [h]
  · have h0 : (d == 0) = false := by simpa using h
    simp only [eq_leaf, h0, ofBool_false, label_leaf, ne_eq, not_true_eq_false, ↓reduceIte, h]
    exact rename_eq t (fun j ↦ Const.sub j (leaf d)) (· - d) fun j ↦ rfl

/-- The mirror's matching of a pattern's variable. -/
theorem matchVar_eq (i d : ℕ) (t : Term) (σ : List (Option Term)) :
    «Prover.matchVar» (leaf i) (leaf d) (encTerm t) (σ.map encOT) =
      encOpt ((Internal.matchVar i d t σ).map encSigma) := by
  simp only [«Prover.matchVar», template, Internal.matchVar, lowerBy_eq]
  generalize (if d = 0 then t else Internal.Term.rename t (· - d)) = t'
  rw [rename_eq t' (fun j ↦ Const.add j (leaf d)) (· + d) fun j ↦ rfl]
  mirror_simp [sub_leaf, encTerm_eq_iff, mVar_eq, List.getElem?_map, none_eq, some_eq]
  by_cases h1 : i < d
  · by_cases h2 : t = Internal.Term.var i <;> simp [h1, h2, encSigma]
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases h3 : d = 0 ∨ (t'.rename fun x ↦ x + d) = t
    · have h3' : (d == 0 || decide ((t'.rename fun x ↦ x + d) = t)) = true := by
        rcases h3 with h3 | h3 <;> simp [h3]
      simp only [h3', h3, ↓reduceIte]
      rcases σ[i - d]? with _ | _ | s
      · by_cases h4 : t' = Internal.Term.var (i - d) <;> simp [h4, encSigma]
      · simp [encOT, encSigma, setAt_eq, List.map_set, encOpt, «Prelude.isSome», ofBool]
      · by_cases h4 : s = t' <;>
          simp [h4, encOT, encSigma, encOpt, «Prelude.isSome», «Prelude.get»,
            ofBool]
    · have h3' : (d == 0 || decide ((t'.rename fun x ↦ x + d) = t)) = false := by
        simp only [not_or] at h3
        simp [h3]
      simp [h3', h3]

/-- A list of matchings without its head. -/
@[simp] theorem mtTail_eq (rs : List (Tree → Tree → List Tree → Tree)) :
    «Prover/Mts.tail» rs = rs.tail := by
  cases rs <;> rfl

/-- The matching of a child at a position, one matching nothing out of range. -/
@[simp] theorem mtAt_eq (rs : List (Tree → Tree → List Tree → Tree)) (i : ℕ) :
    «Prover.mtAt» rs (leaf i) = rs[i]?.getD fun _ _ _ ↦ «Prelude.none» := by
  have hr : ∀ i : ℕ, Nat.repeat «Prover/Mts.tail» i rs = rs.drop i :=
    Nat.rec rfl fun i ih ↦ by rw [Nat.repeat, ih, mtTail_eq, List.tail_drop]
  simp only [«Prover.mtAt», template, iter_leaf, hr]
  cases h : rs.drop i with
  | nil =>
    rw [List.drop_eq_nil_iff] at h
    rw [List.getElem?_eq_none h]
    rfl
  | cons r rest =>
    rw [← List.head?_drop, h]
    rfl

/-- The mirror's matching of terms by a list of matchings, one after another, from an
encoded assignment, at related matchings: the fold of the matchings into functions of the terms. -/
theorem foldr_match_eq (d : ℕ) :
    ∀ (xs : List (Term × (Tree → Tree → List Tree → Tree) ×
        (ℕ → Term → List (Option Term) → Option (List (Option Term))))),
      (∀ x ∈ xs, MRel x.2.1 x.2.2) → ∀ (us : List Term) (acc : Option (List (Option Term))),
      List.foldr (fun q k ts a ↦ Const.lcase ts a fun u rest ↦
          k rest («Base.bindO» a fun sn ↦ q (leaf d) u (Const.children sn)))
        (fun _ a ↦ a) (xs.map fun x ↦ x.2.1) (us.map encTerm) (encOpt (acc.map encSigma)) =
      encOpt ((((xs.map fun x ↦ (x.1, x.2.2)).zip us).foldl
        (fun acc (q, u) ↦ acc.bind (q.2 d u)) acc).map encSigma) :=
  List.rec (fun _ us acc ↦ by cases us <;> rfl) fun x xs ih hx us acc ↦ by
    rcases us with _ | ⟨u, us⟩
    · rfl
    · simp only [List.map_cons, List.foldr_cons, lcase_cons, List.zip_cons_cons, List.foldl_cons,
        bindO_eq]
      have ih' := ih fun y hy ↦ hx y (List.mem_cons_of_mem x hy)
      rcases acc with _ | σ
      · exact ih' us none
      · have hm : x.2.1 (leaf d) (encTerm u) (Const.children (encSigma σ)) =
            encOpt (((some σ).bind (x.2.2 d u)).map encSigma) := by
          rw [Option.bind_some, children_eq, encSigma, RoseTree.children_node]
          exact hx x List.mem_cons_self d u σ
        simp only [Option.map_some, Option.elim_some, hm]
        exact ih' us _

/-- The mirror's matching of the children of a pattern against a term's, one after another,
at related matchings of the pattern's children. -/
theorem matchAll_eq (d : ℕ) (v : Tree → Tree → List Tree → Tree)
    (xs : List (Term × (Tree → Tree → List Tree → Tree) ×
      (ℕ → Term → List (Option Term) → Option (List (Option Term)))))
    (hx : ∀ x ∈ xs, MRel x.2.1 x.2.2) (us : List Term) (σ : List (Option Term)) :
    «Prover.matchAll» (v :: xs.map fun x ↦ x.2.1) (leaf d) (us.map encTerm)
        (σ.map encOT) =
      encOpt ((((xs.map fun x ↦ (x.1, x.2.2)).zip us).foldl
        (fun acc (q, u) ↦ acc.bind (q.2 d u)) (some σ)).map encSigma) := by
  simp only [«Prover.matchAll», template, foldr_eq, mtTail_eq, List.tail_cons]
  exact foldr_match_eq d xs hx us (some σ)

/-- Two labels' positions and data are equal exactly when the labels are. -/
theorem labelData_beq (l l' : Internal.Label) :
    ((labelData l).1 == (labelData l').1 &&
      decide (RoseTree.node 0 (labelData l).2 = RoseTree.node 0 (labelData l').2)) =
      decide (l = l') := by
  by_cases h : l = l'
  · subst h
    simp
  · have : ¬((labelData l).1 = (labelData l').1 ∧
        RoseTree.node 0 (labelData l).2 = RoseTree.node 0 (labelData l').2) :=
      fun ⟨h1, h2⟩ ↦ h (labelData_inj l l' h1 h2)
    rw [decide_eq_false h, Bool.eq_false_iff]
    simpa only [ne_eq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using this

/-- The data node of an encoded term's label. -/
@[simp] theorem child_encTerm (t : Term) :
    Const.child (encTerm t) (leaf 0) = RoseTree.node 0 (labelData t.label).2 := by
  rw [← RoseTree.node_label_children t, encTerm_node]
  rfl

/-- The mirror's step of the matching of a pattern at an encoded node other than a variable. -/
theorem matchNode_eq (l : Internal.Label) (hl : ∀ i, l ≠ .var i)
    (v : Tree → Tree → List Tree → Tree)
    (xs : List (Term × (Tree → Tree → List Tree → Tree) ×
      (ℕ → Term → List (Option Term) → Option (List (Option Term)))))
    (hx : ∀ x ∈ xs, MRel x.2.1 x.2.2) (d : ℕ) (t : Term) (σ : List (Option Term)) :
    «Prover.matchStep» (encTerm (RoseTree.node l (xs.map Prod.fst)))
        (v :: xs.map fun x ↦ x.2.1) (leaf d) (encTerm t) (σ.map encOT) =
      encOpt ((Internal.matchNode l (xs.map fun x ↦ (x.1, x.2.2)) d t σ).map encSigma) := by
  have h0 : (labelData l).1 ≠ 0 := by
    cases l <;> simp_all [labelData]
  simp only [«Prover.matchStep», template, encTerm_node, label_node, eq_leaf,
    child_encTerm, mArgs_eq, length_eq, and_eq, List.length_map, child_node, List.getD_cons_zero,
    Internal.matchNode]
  have h0' : ((labelData l).1 == 0) = false := by simpa using h0
  mirror_simp [h0', «Language.mArgs», label_encTerm, labelData_beq]
  by_cases hc : l = t.label ∧ xs.length = t.children.length
  swap
  · have hc' : (decide (l = t.label) && xs.length == t.children.length) = false := by
      rw [Bool.eq_false_iff]
      simpa [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hc
    simp only [hc', hc, Bool.false_eq_true, ↓reduceIte]
    rfl
  obtain ⟨hl', hlen⟩ := hc
  obtain ⟨us, rfl⟩ : ∃ us, t = RoseTree.node l us :=
    ⟨t.children, by rw [hl']; exact (RoseTree.node_label_children t).symm⟩
  have hm : ∀ x ∈ xs, ∀ d u σ,
      x.2.1 (leaf d) (encTerm u) (σ.map encOT) = encOpt ((x.2.2 d u σ).map encSigma) := hx
  simp only [RoseTree.children_node] at hlen
  simp only [RoseTree.label_node, RoseTree.children_node, hlen, decide_true, beq_self_eq_true,
    Bool.and_self, and_self, ↓reduceIte]
  rw [matchAll_eq d v xs hx us σ]
  cases l with
  | var i => exact absurd rfl (hl i)
  | lam a =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, xs⟩⟩ <;> rcases us with _ | ⟨u0, _ | ⟨u1, us⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    all_goals simp [labelData, hm]
  | natRec | listRec =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, xs⟩⟩⟩⟩ <;>
      rcases us with _ | ⟨u0, _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, us⟩⟩⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    -- more than three children are matched in turn on both sides
    all_goals try (simp [labelData, hm]; done)
    all_goals simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.reduceBEq, Bool.and_false, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Bool.and_true,
      Bool.or_eq_true, List.map_cons, List.map_nil, List.getD_eq_getElem?_getD,
      Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Option.getD_some, mtAt_eq,
      Nat.reduceLT, List.getElem_cons_succ, Nat.lt_add_one, List.zip_cons_cons,
      List.zip_nil_right, List.foldl_cons, Option.bind_some, List.foldl_nil, Option.map_bind,
      Function.comp_apply, labelData]
    all_goals
      simp only [true_or, or_true, ↓reduceIte, add_leaf, hm x0 (by simp), bindO_eq]
      rcases x0.2.2 d u0 σ with _ | σ₁
      · rfl
      · simp only [Option.map_some, Option.elim_some, encSigma, RoseTree.children_node,
          hm x1 (by simp), bindO_eq, Option.bind_some]
        rcases x1.2.2 _ u1 σ₁ with _ | σ₂
        · rfl
        · simp only [Option.map_some, Option.elim_some, encSigma, RoseTree.children_node,
            hm x2 (by simp), Option.bind_some]
  | roseRec c =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;>
      rcases us with _ | ⟨u0, _ | ⟨u1, _ | ⟨u2, us⟩⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    all_goals simp [labelData, hm, «Language.mArg», «Language.mArgs»]
    all_goals
      by_cases h1 : x0.1 = u0 <;> simp [h1, «Prelude.none», encOpt]
  | _ => simp [labelData]

/-- The mirror's step of the matching of a pattern at an encoded node is the matching's step at
the node, at related matchings of the children. -/
theorem matchStep_eq (l : Internal.Label) (v : Tree → Tree → List Tree → Tree)
    (xs : List (Term × (Tree → Tree → List Tree → Tree) ×
      (ℕ → Term → List (Option Term) → Option (List (Option Term)))))
    (hx : ∀ x ∈ xs, MRel x.2.1 x.2.2) :
    MRel («Prover.matchStep» (encTerm (RoseTree.node l (xs.map Prod.fst)))
        (v :: xs.map fun x ↦ x.2.1))
      (Internal.matchStep l (xs.map fun x ↦ (x.1, x.2.2))) := by
  intro d t σ
  cases l with
  | var i =>
    have : «Language.mD» (encTerm (RoseTree.node (.var i) (xs.map Prod.fst))) (leaf 0) =
        leaf i := by
      rw [mD_eq]
      rfl
    simp only [«Prover.matchStep», template, this]
    exact matchVar_eq i d t σ
  | _ => exact matchNode_eq _ (fun _ h ↦ by cases h) v xs hx d t σ

/-- The mirror's matching of an encoded pattern. -/
theorem matchTerm_eq (p : Term) :
    MRel («Prover.matchTerm» (encTerm p)) (Internal.matchTerm p) :=
  para_enc _ _ MRel «Prover.matchStep» Internal.matchStep
    (fun l v xs hx ↦ matchStep_eq l v xs hx) p

/-! The rewriting of a term at its root. -/

variable (G : Internal.Globals) (E : Array Internal.Entry) (n : ℕ) (Γ : List Tree)
  (Φ : List Term)

/-- The mirror's rewriting of an encoded term at its root by the checker's rule of a position
and data, with the derivation of the rule. -/
theorem ruleStep_eq (l : Internal.Rule) (t : Term) :
    «Base.mapO»
        (fun t₂ ↦ «Language.pr» t₂
          («Prover.dNode» (leaf (ruleData l).1) (ruleData l).2 []))
        («Derivation.rootStep» (encGlobals G) (E.toList.map encEntry) (leaf n) Γ
          (Φ.map encTerm) (leaf (ruleData l).1) (ruleData l).2 (encTerm t)) =
      encOpt ((Internal.rootStep G E n Γ Φ l t).map fun t' ↦ encTD (t', RoseTree.node l [])) := by
  rw [rootStep_eq G E n Γ Φ, mapO_eq, Option.map_map]
  rfl

/-- The mirror's rewriting of an encoded term at its root by a theorem of an index at objects,
its instance found by a matching related to a matching of its left side's {lit}`k` variables. -/
theorem thmRewrite_eq (j : ℕ) (θ : List Tree) (m' : Tree → Tree → List Tree → Tree)
    (m : ℕ → Term → List (Option Term) → Option (List (Option Term))) (hm : MRel m' m) (k : ℕ)
    (t : Term) :
    «Prover.thmRewrite» (encGlobals G) (E.toList.map encEntry) (leaf n) Γ
        (Φ.map encTerm) (leaf j) θ m' (leaf k) (encTerm t) =
      encOpt ((do
        let σ ← m 0 t (List.replicate k none)
        let σ ← σ.mapM id
        let l := Internal.Rule.thm j θ σ false
        (Internal.rootStep G E n Γ Φ l t).map fun t' ↦ (t', RoseTree.node l [])).map encTD) := by
  have hr : «Prelude.replicate» (leaf k) «Prelude.none» =
      (List.replicate k (none : Option Term)).map encOT := by
    rw [replicate_eq, List.map_replicate]
    rfl
  simp only [«Prover.thmRewrite», template, hr, hm 0 t, bindO_eq]
  rcases m 0 t (List.replicate k none) with _ | σ
  · rfl
  · have hs : Const.children (encSigma σ) = σ.map fun o ↦ encOpt (o.map encTerm) := by
      simp [encSigma, encOT]
    simp only [Option.map_some, Option.elim_some, hs, allSomeT_eq,
      Infer.mapM_map_option (fun o : Option Term ↦ o) encTerm]
    change «Base.bindO» (encOpt (((σ.mapM id).map (List.map encTerm)).map
      (RoseTree.node 0))) _ = _
    simp only [Option.bind_eq_bind, Option.bind_some]
    rcases σ.mapM id with _ | σ'
    · rfl
    · have hd := ruleStep_eq G E n Γ Φ (.thm j θ σ' false) t
      simp only [ruleData, ofBool_false] at hd
      simp only [Option.map_some, bindO_eq, Option.elim_some, «Theory.l4»,
        «Theory.l3», «Theory.l2», single_eq, node_leaf]
      rw [hd, Option.bind_some, Option.map_map]
      rfl

/-- The mirror's rewriting of an encoded term at its root by a rule related to a rule of the
normalizer. -/
theorem tryRule_eq (r' : Tree × (Tree → Tree → List Tree → Tree)) (r : NormRule)
    (h : RRel r' r) (t : Term) :
    «Prover.tryRule» (encGlobals G) (E.toList.map encEntry) (leaf n) Γ
        (Φ.map encTerm) r' (encTerm t) =
      encOpt ((Internal.tryRule G E n Γ Φ t r).map encTD) := by
  cases r with
  | rule l =>
    simp only [RRel] at h
    simp only [«Prover.tryRule», template, h, encRule]
    mirror_simp [List.getD_cons_zero]
    rw [ruleStep_eq G E n Γ Φ l t]
    simp only [Internal.tryRule, Option.map_map]
    rfl
  | delta k =>
    simp only [RRel] at h
    simp only [«Prover.tryRule», template, h, encRule]
    have hd := ruleStep_eq G E n Γ Φ .delta t
    simp only [ruleData] at hd
    mirror_simp [List.getD_cons_zero, label_encTerm, mD_eq, hd]
    obtain ⟨lt, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
      ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩
    cases lt with
    | defn k' θ =>
      by_cases hk : k = k'
      · subst hk
        simp [labelData, Internal.tryRule, Option.map_map]
        rfl
      · simp [labelData, Internal.tryRule, hk, Ne.symm hk, none_eq]
    | _ => simp [labelData, Internal.tryRule, none_eq]
  | deltaBelow m ks =>
    simp only [RRel] at h
    simp only [«Prover.tryRule», template, h, encRule]
    have hd := ruleStep_eq G E n Γ Φ .delta t
    simp only [ruleData] at hd
    have ha : ∀ k' : ℕ, «Base.anyT» (fun x ↦ Const.eq x (leaf k')) (ks.map leaf) =
        ofBool (decide (k' ∈ ks)) := fun k' ↦ by
      rw [anyT_eq (fun x ↦ Const.eq x (leaf k')) (fun x ↦ x.label == k') _ fun _ _ ↦ rfl]
      simp only [List.any_map, Function.comp_def, label_leaf]
      congr 1
      rw [Bool.eq_iff_iff]
      simp [List.any_eq_true]
    mirror_simp [List.getD_cons_zero, label_encTerm, mD_eq, hd]
    obtain ⟨lt, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
      ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩
    cases lt with
    | defn k' θ =>
      simp only [labelData]
      by_cases h1 : k' < m
      · by_cases h2 : k' ∈ ks
        · simp [h1, h2, ha, Internal.tryRule, none_eq]
        · simp [h1, h2, ha, Internal.tryRule, Option.map_map]
          rfl
      · simp [h1, ha, Internal.tryRule, none_eq]
    | _ => simp [labelData, Internal.tryRule, none_eq]
  | unitVar =>
    simp only [RRel] at h
    simp only [«Prover.tryRule», template, h, encRule]
    have hd := ruleStep_eq G E n Γ Φ .unitEta t
    simp only [ruleData] at hd
    mirror_simp [List.getD_cons_zero, label_encTerm, mD_eq, hd]
    obtain ⟨lt, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
      ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩
    cases lt with
    | var i =>
      simp only [labelData]
      by_cases hk : Γ[i]? = some one
      · simp [hk, Internal.tryRule, Option.map_map, some_eq]
        rfl
      · simp [hk, Internal.tryRule, none_eq, some_eq, encOpt_inj]
    | _ => simp [labelData, Internal.tryRule, none_eq]
  | hyp i =>
    simp only [RRel] at h
    simp only [«Prover.tryRule», template, h, encRule]
    have hd := ruleStep_eq G E n Γ Φ (.rwHyp i false) t
    simp only [ruleData, ofBool_false] at hd
    mirror_simp [List.getD_cons_zero, «Theory.l2», hd]
    simp only [Internal.tryRule, Option.map_map]
    rfl
  | thmAt j θ root m k =>
    obtain ⟨p, hp, h1, hm⟩ := h
    simp only [«Prover.tryRule», template, h1]
    mirror_simp [List.getD_cons_zero, List.getD_cons_succ, sameShape_eq, hp]
    by_cases hs : Internal.sameShape root t.label
    · simp [hs, Internal.tryRule, thmRewrite_eq G E n Γ Φ j θ _ m hm k t]
    · simp [hs, Internal.tryRule, none_eq]
  | thm j θ =>
    simp only [RRel] at h
    simp only [«Prover.tryRule», template, h, encRule]
    mirror_simp [List.getD_cons_zero, List.getD_cons_succ, Array.getElem?_toList,
      entryLanguage_eq]
    simp only [Internal.tryRule, Option.bind_eq_bind]
    rcases E[j]? with _ | (a | s)
    · rfl
    · simp only [Option.map_some, Option.elim_some, entryLanguage_eq, Internal.Entry.language?,
        bindO_eq, thConcl_eq, eqParts_eq, Option.bind_some]
      rcases Internal.eqParts a.concl with _ | ⟨l, r⟩
      · rfl
      · have hp : (if θ.isEmpty = true then encTerm l
            else «Language.osubst» θ (encTerm l)) =
            encTerm (if θ.isEmpty then l else l.osubst θ) := by
          split <;> simp [osubst_eq]
        simp only [Option.map_some, Option.elim_some, p1_eq, sameShape_eq, hp, thCtx_eq,
          thmRewrite_eq G E n Γ Φ j θ _ _ (matchTerm_eq _) _ t, Option.bind_some]
        by_cases hs : Internal.sameShape l.label t.label <;> simp [hs, none_eq]
    · simp [Internal.Entry.language?, none_eq]

/-- The mirror's first rule of a list that rewrites an encoded term at its root, at a list of
rules related to the normalizer's. -/
theorem rootRewrite_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree)))
    (rs : List NormRule) (h : List.Forall₂ RRel rs' rs) (t : Term) :
    «Prover.rootRewrite» (encGlobals G) (E.toList.map encEntry) (leaf n) rs' Γ
        (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.rootRewrite G E n rs Γ Φ t).map encTD) := by
  simp only [«Prover.rootRewrite», template, foldr_eq, Internal.rootRewrite]
  revert rs
  exact rs'.rec (fun rs h ↦ by cases h; rfl) fun r' rs' ih rs h ↦ by
    cases h with
    | cons hr h' =>
      simp only [List.foldr_cons, List.findSome?_cons, tryRule_eq G E n Γ Φ _ _ hr t, isSome_eq,
        ih _ h']
      rcases Internal.tryRule G E n Γ Φ t _ with _ | x <;> rfl

/-- The mirror's preparation of an encoded rule other than a prepared theorem. -/
theorem prepareRule_eq (r : NormRule) (hr : ∀ j θ root m k, r ≠ .thmAt j θ root m k) :
    RRel («Prover.prepareRule» (E.toList.map encEntry) (encRule r))
      (Internal.prepareRule E r) := by
  cases r with
  | thm j θ =>
    simp only [«Prover.prepareRule», template, encRule]
    mirror_simp [List.getD_cons_zero, List.getD_cons_succ, Array.getElem?_toList]
    simp only [Internal.prepareRule]
    rcases E[j]? with _ | (a | s)
    · rfl
    · simp only [Option.map_some, Option.elim_some, entryLanguage_eq, Internal.Entry.language?,
        bindO_eq, thConcl_eq, eqParts_eq, Option.bind_some, Option.elim_some]
      rcases Internal.eqParts a.concl with _ | ⟨l, r⟩
      · rfl
      · have hp : (if θ.isEmpty = true then encTerm l
            else «Language.osubst» θ (encTerm l)) =
            encTerm (if θ.isEmpty then l else l.osubst θ) := by
          split <;> simp [osubst_eq]
        simp only [Option.map_some, isSome_eq, Option.isSome_some, tmpl_fromMaybe_eq,
          Option.getD_some, p1_eq, thCtx_eq, hp, ofBool_bne, ↓reduceIte]
        refine ⟨if θ.isEmpty then l else l.osubst θ, rfl, ?_, matchTerm_eq _⟩
        simp []
    · rfl
  | thmAt j θ root m k => exact absurd rfl (hr j θ root m k)
  | _ => rfl

/-- The mirror's preparation of encoded rules none of which is a prepared theorem. -/
theorem prepareRules_eq (rs : List NormRule)
    (hr : ∀ r ∈ rs, ∀ j θ root m k, r ≠ .thmAt j θ root m k) :
    List.Forall₂ RRel
      («Prover.prepareRules» (E.toList.map encEntry) (rs.map encRule))
      (Internal.prepareRules E rs) := by
  have h : ∀ ts : List Tree, «Prover.prepareRules» (E.toList.map encEntry) ts =
      ts.map («Prover.prepareRule» (E.toList.map encEntry)) :=
    List.rec rfl fun t ts ih ↦ by
      simp only [«Prover.prepareRules», template, foldr_eq, List.foldr_cons] at ih ⊢
      rw [ih]
      rfl
  rw [h, List.map_map, Internal.prepareRules, List.forall₂_map_left_iff,
    List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun r hm ↦ prepareRule_eq E r (hr r hm)

/-! Normalization innermost first. -/

/-- The mirror's normalization and a normalization are related when they agree at every context,
encoded hypotheses and encoded term. -/
def NRel (v : List Tree → List Tree → Tree → Tree)
    (w : List Tree → List Term → Term → Option (Term × Deriv × Bool)) : Prop :=
  ∀ Γ Φ t, v Γ (Φ.map encTerm) (encTerm t) = encOpt ((w Γ Φ t).map encTDB)

/-- The mirror's pairs of two lists, at the positions of the shorter. -/
@[simp] theorem zipTs_eq (xs ys : List Tree) :
    «Prover.zipTs» xs ys = (xs.zip ys).map fun p ↦ encPair p := by
  simp only [«Prover.zipTs», template, foldr_eq]
  revert ys
  exact xs.rec (fun ys ↦ by cases ys <;> rfl) fun x xs ih ys ↦ by
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [List.foldr_cons, lcase_cons]
      rw [ih]
      rfl

/-- The mirror's node rebuilt from the terms of its children's reductions. -/
@[simp] theorem rebuild_eq (l : Internal.Label) (ts : List Term) (cs : List (Term × Deriv × Bool)) :
    «Prover.rebuild» (encTerm (RoseTree.node l ts)) (cs.map encTDB) =
      encTerm (RoseTree.node l (cs.map Prod.fst)) := by
  simp [«Prover.rebuild», template, encTerm_node, encTDB, List.map_map, Function.comp_def]

/-- The mirror's test whether a child's reduction rewrote. -/
@[simp] theorem marked_eq (cs : List (Term × Deriv × Bool)) :
    «Prover.marked» (cs.map encTDB) = ofBool (cs.any (·.2.2)) :=
  List.rec rfl (fun c cs ih ↦ by
    simp only [«Prover.marked», template, «Base.anyT», foldr_eq, List.map_cons,
      List.foldr_cons, List.any_cons] at ih ⊢
    rw [ih]
    rcases c with ⟨t, d, _ | _⟩ <;> rfl) cs

/-- The mirror's step of the normalization innermost first, at related rules and normalizations
of the subterms. -/
theorem normStep_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (rec' : List Tree → List Tree → Tree → Tree)
    (rec : List Tree → List Term → Term → Option (Term × Deriv × Bool)) (hrec : NRel rec' rec) :
    NRel («Prover.normStep» (encGlobals G) (E.toList.map encEntry) (leaf n) rs' rec')
      (Internal.normStep G E n rs rec) := by
  intro Γ Φ t
  obtain ⟨l, ts, rfl⟩ : ∃ l ts, t = RoseTree.node l ts :=
    ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩
  simp only [«Prover.normStep», template, childCtxs_eq, Internal.normStep, RoseTree.label_node,
    RoseTree.children_node, bindO_eq, Option.bind_eq_bind]
  have hr : ∀ Γ Φ t, rec' Γ (Φ.map encTerm) (encTerm t) = encOpt ((rec Γ Φ t).map encTDB) := hrec
  rcases Internal.childCtxs G n l ts Γ Φ with _ | Γs
  · rfl
  simp only [Option.map_some, Option.elim_some, Option.bind_some, children_eq,
    RoseTree.children_node, mArgs_eq, zipTs_eq, mapT_eq, List.map_map, Function.comp_def,
    List.zip_map, encCtx, p1_eq, p2_eq, Prod.map, hr, template, Derivation.scopesOf_node,
    Derivation.scopeCtx_pair, Derivation.scopeHyps_pair]
  rw [allSomeT_eq (fun x ↦ (rec x.1.1 x.1.2 x.2).map encTDB) (Γs.zip ts),
    Infer.mapM_map_option (fun x : (List PartialHorn.Tree × List Term) × Term ↦
      rec x.1.1 x.1.2 x.2) encTDB]
  generalize List.mapM (fun x : (List PartialHorn.Tree × List Term) × Term ↦
    rec x.1.1 x.1.2 x.2) (Γs.zip ts) = oc
  rcases oc with _ | cs
  · rfl
  have hc := dNode_eq .cong (cs.map fun c ↦ c.2.1)
  simp only [ruleData, List.map_map, Function.comp_def] at hc
  have hd : (if (ofBool (cs.any fun c ↦ c.2.2)).label ≠ 0 then
      «Language.pr» («Prover.dNode» (leaf 2) []
        (cs.map fun c ↦ encDeriv c.2.1)) (leaf 1) else «Prover.dRefl») =
      encDB (if cs.any (·.2.2) then (RoseTree.node .cong (cs.map (·.2.1)), true)
        else Internal.dRefl) := by
    cases cs.any fun c ↦ c.2.2
    · rfl
    · simp only [ofBool_true, label_leaf, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, hc]
      rfl
  simp only [Option.map_some, bindO_eq, Option.elim_some, RoseTree.children_node, rebuild_eq,
    marked_eq, rootRewrite_eq G E n Γ Φ rs' rs hrs, isSome_eq, Option.bind_some, List.map_map,
    Function.comp_def, p2_encTDB, p1_encDB, hd]
  generalize (if (cs.any fun x ↦ x.2.2) = true then
    (RoseTree.node Internal.Rule.cong (List.map (fun x ↦ x.2.1) cs), true) else Internal.dRefl) = d₁
  rcases Internal.rootRewrite G E n rs Γ Φ (RoseTree.node l (List.map Prod.fst cs)) with
    _ | ⟨t₂, dr⟩
  · rfl
  · simp only [Option.map_some, Option.isSome_some, ofBool_true, label_leaf, ne_eq,
      one_ne_zero, not_false_eq_true, ↓reduceIte, tmpl_fromMaybe_eq, Option.map_bind,
      Option.pure_def,
      Option.getD_some, p1_encTD, p2_encTD, hr, mapO_eq, Option.map_map]
    rcases rec Γ Φ t₂ with _ | ⟨t₃, d₃⟩
    · rfl
    · have h2 : «Language.pr» (encDeriv dr) (leaf 1) = encDB (dr, true) := rfl
      simp only [Option.map_some, Option.bind_some, Function.comp_apply, p1_encTDB, p2_encTDB,
        h2, dTrans_eq]
      rfl

/-- The mirror's normalization innermost first within a depth of fuel, at related rules. -/
theorem normalize_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) :
    NRel («Prover.normalize» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (leaf fuel))
      (Internal.normalize G E n rs fuel) := by
  simp only [«Prover.normalize», template, iter_leaf, Internal.normalize]
  exact Nat.rec (fun _ _ _ ↦ rfl)
    (fun k ih ↦ by rw [Nat.repeat]; exact normStep_eq G E n rs' rs hrs _ _ ih) fuel

/-- The mirror's proof of an equation by reducing both sides, by related reductions, to one
term. -/
theorem joinBy_eq (v : List Tree → List Tree → Tree → Tree)
    (w : List Tree → List Term → Term → Option (Term × Deriv × Bool)) (h : NRel v w)
    (Γ : List Tree) (Φ : List Term) (t u : Term) :
    «Prover.joinBy» v Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((do
        let (v₁, d₁, _) ← w Γ Φ t
        let (v₂, d₂, _) ← w Γ Φ u
        if v₁ = v₂ then some (RoseTree.node Internal.Rule.join [d₁, d₂]) else none).map
          encDeriv) := by
  simp only [«Prover.joinBy», template, h Γ Φ t, h Γ Φ u, bindO_eq]
  rcases w Γ Φ t with _ | ⟨v₁, d₁, b₁⟩
  · rfl
  rcases w Γ Φ u with _ | ⟨v₂, d₂, b₂⟩
  · rfl
  have hj := dNode_eq .join [d₁, d₂]
  simp only [ruleData, List.map_cons, List.map_nil] at hj
  by_cases hv : v₁ = v₂ <;>
    simp [hv, encTDB, encDB, p1_eq, p2_eq, encTerm_eq_iff, hj, «Theory.l2»,
      none_eq, some_eq]

/-- The mirror's proof of an equation by normalizing both sides to one term. -/
theorem byNorm_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t u : Term) :
    «Prover.byNorm» (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf fuel) Γ
        (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byNorm G E n rs fuel Γ Φ t u).map encDeriv) := by
  rw [«Prover.byNorm», joinBy_eq _ _ (normalize_eq G E n rs' rs hrs fuel)]
  rfl

/-! Induction. -/

/-- The mirror's instance of a term at a primitive arrow's element for its innermost variable. -/
@[simp] theorem instAt_eq (k : ℕ) (θ : List Tree) (t : Term) :
    «Prover.instAt» (leaf k) θ (encTerm t) =
      encTerm (t.subst (Internal.instVar (Term.arr k θ Term.star))) := by
  simp only [«Prover.instAt», template, mStar_eq, mArr_eq]
  exact subst_eq _ _ _ (instVar_eq _)

/-- A derivation's node as a tree. -/
theorem encDeriv_node (r : Internal.Rule) (cs : List Deriv) :
    encDeriv (RoseTree.node r cs) =
      RoseTree.node (ruleData r).1 (RoseTree.node 0 (ruleData r).2 :: cs.map encDeriv) :=
  encWith_node _ _ r cs

/-- The mirror's weakening of encoded hypotheses past two new innermost variables. -/
theorem mapT_weaken2 (Φ : List Term) :
    «Base.mapT» «Derivation.weaken2» (Φ.map encTerm) =
      (Φ.map Internal.weaken2).map encTerm := by
  simp [List.map_map, Function.comp_def]

/-- The mirror's weakening of encoded hypotheses past a new innermost variable. -/
theorem mapT_weaken1 (Φ : List Term) :
    «Base.mapT» «Derivation.weaken1» (Φ.map encTerm) =
      (Φ.map Internal.weaken1).map encTerm := by
  simp [List.map_map, Function.comp_def]

/-- Encoded hypotheses followed by an encoded formula. -/
theorem snocHyp_eq (Φ : List Term) (φ : Term) :
    «Prelude.append» (Φ.map encTerm) [encTerm φ] = (Φ ++ [φ]).map encTerm := by
  simp

/-- The simplification of a case of the mirror's induction: the options, lists and pairs of the
program, the checker's instances, and the given lemmas, the maps of encodings left unfused so
that the proofs by normalization apply. -/
local macro "ind_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [bindO_eq, mapO_eq, children_eq, RoseTree.children_node, lcase_cons, lcase_nil,
    lowerHyps_eq, natSuccAt_eq, listConsAt_eq, weakenElem_eq, instAt_eq, subst_atVar0, mEq_eq,
    single_eq, length_eq, mapT_weaken2, mapT_weaken1, snocHyp_eq, p1_encTDB, p2_encTDB,
    p1_encDB, p2_encDB, Option.bind_eq_bind, Option.pure_def, Option.map_bind, Option.bind_map,
    Option.map_map, Option.elim_some, Option.elim_none, Option.map_some, Option.map_none,
    Option.bind_some, Option.bind_none, Function.comp_def, none_eq, some_eq, elim_encOpt,
    «Theory.l3», «Theory.l2», encDeriv_node, ruleData,
    «Prover.dNode», «Language.mNode», node_leaf, List.map_cons, List.map_nil,
    $ls,*])

/-- The mirror's proof of an equation by induction on a natural number variable with a step,
each premise by normalization. -/
theorem byNatInd_eq (kz ks : ℕ) (s : Term) (rs' : List (Tree × (Tree → Tree → List Tree → Tree)))
    (rs : List NormRule) (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) :
    «Prover.byNatInd» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kz)
        (leaf ks) (encTerm s) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byNatInd G E n kz ks s rs fuel Γ Φ t u).map encDeriv) := by
  rcases Γ with _ | ⟨c, Γ'⟩
  · rfl
  simp only [«Prover.byNatInd», template, Internal.byNatInd]
  ind_simp [byNorm_eq G E n rs' rs hrs]
  rcases Internal.lowerHyps G n Γ' Φ with _ | Φ'
  · rfl
  ind_simp [byNorm_eq G E n rs' rs hrs]
  simp only [Option.map_eq_bind, Function.comp_def]

/-- The mirror's rules followed by the rewriting by the hypothesis of an index. -/
theorem withHyp_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (i : ℕ) :
    List.Forall₂ RRel («Prover.withHyp» rs' (leaf i)) (rs ++ [.hyp i]) := by
  have h : ∀ rs' : List (Tree × (Tree → Tree → List Tree → Tree)),
      «Prover.withHyp» rs' (leaf i) =
        rs' ++ [(RoseTree.node 6 [leaf i], «Prover.noMatch»)] :=
    List.rec rfl fun r rs' ih ↦ by
      simp only [«Prover.withHyp», template, foldr_eq, List.foldr_cons] at ih ⊢
      rw [ih]
      rfl
  rw [h]
  exact List.rel_append hrs (List.Forall₂.cons rfl List.Forall₂.nil)

/-- The mirror's proof of an equation by induction on a list variable with a step, each premise
by normalization. -/
theorem byListInd_eq (kn kc : ℕ) (s : Term) (rs' : List (Tree × (Tree → Tree → List Tree → Tree)))
    (rs : List NormRule) (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) :
    «Prover.byListInd» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn)
        (leaf kc) (encTerm s) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byListInd G E n kn kc s rs fuel Γ Φ t u).map encDeriv) := by
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
theorem byNatIndHyp_eq (kz ks : ℕ) (rs' : List (Tree × (Tree → Tree → List Tree → Tree)))
    (rs : List NormRule) (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) :
    «Prover.byNatIndHyp» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kz)
        (leaf ks) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byNatIndHyp G E n kz ks rs fuel Γ Φ t u).map encDeriv) := by
  rcases Γ with _ | ⟨c, Γ'⟩
  · rfl
  have hN : ∀ Γ Φ t, «Prover.normalize» (encGlobals G) (E.toList.map encEntry)
      (leaf n) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.normalize G E n rs fuel Γ Φ t).map encTDB) :=
    normalize_eq G E n rs' rs hrs fuel
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
  rcases Internal.normalize G E n rs fuel (c :: Γ') (Φ ++ [t.eq u]) (t.eq u) with _ | ⟨ψ, dψ, b⟩
  · rfl
  ind_simp [hN, hW, List.length_map, List.length_append, List.length_singleton]

/-- The mirror's proof of an equation by induction on a list variable with the induction
hypothesis. -/
theorem byListIndHyp_eq (kn kc : ℕ) (rs' : List (Tree × (Tree → Tree → List Tree → Tree)))
    (rs : List NormRule) (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) :
    «Prover.byListIndHyp» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn)
        (leaf kc) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byListIndHyp G E n kn kc rs fuel Γ Φ t u).map encDeriv) := by
  rcases Γ with _ | ⟨c, Γ'⟩
  · rfl
  have hN : ∀ Γ Φ t, «Prover.normalize» (encGlobals G) (E.toList.map encEntry)
      (leaf n) rs' (leaf fuel) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.normalize G E n rs fuel Γ Φ t).map encTDB) :=
    normalize_eq G E n rs' rs hrs fuel
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
  rcases Internal.normalize G E n rs fuel (c :: a :: Γ')
    (Φ'.map Internal.weaken2 ++ [Internal.weakenElem (t.eq u)]) (Internal.weakenElem (t.eq u))
    with _ | ⟨ψ, dψ, b⟩
  · rfl
  ind_simp [hN, hW, List.length_map, List.length_append, List.length_singleton]

/-! The reduction to a depth. -/

/-- A list of use counts without its head. -/
@[simp] theorem ufTail_eq (rs : List (Tree → Tree)) : «Prover/UFs.tail» rs = rs.tail := by
  cases rs <;> rfl

/-- The use count of a child at a position, none out of range. -/
@[simp] theorem ufAt_eq (rs : List (Tree → Tree)) (i : ℕ) :
    «Prover.ufAt» rs (leaf i) = rs[i]?.getD fun _ ↦ leaf 0 := by
  have hr : ∀ i : ℕ, Nat.repeat «Prover/UFs.tail» i rs = rs.drop i :=
    Nat.rec rfl fun i ih ↦ by rw [Nat.repeat, ih, ufTail_eq, List.tail_drop]
  simp only [«Prover.ufAt», template, iter_leaf, hr]
  cases h : rs.drop i with
  | nil =>
    rw [List.drop_eq_nil_iff] at h
    rw [List.getElem?_eq_none h]
    rfl
  | cons r rest =>
    rw [← List.head?_drop, h]
    rfl

/-- The mirror's sum of the children's use counts at a variable. -/
theorem ufSum_eq (v : Tree → Tree) (d : ℕ) :
    ∀ xs : List (Term × (Tree → Tree) × (ℕ → ℕ)), (∀ x ∈ xs, ∀ d, x.2.1 (leaf d) = leaf (x.2.2 d)) →
      «Prover.ufSum» (v :: xs.map fun x ↦ x.2.1) (leaf d) =
        leaf ((xs.map fun x ↦ x.2.2 d).sum) :=
  List.rec (fun _ ↦ rfl) fun x xs ih hx ↦ by
    have ih' := ih fun y hy ↦ hx y (List.mem_cons_of_mem x hy)
    simp only [«Prover.ufSum», template, foldr_eq, ufTail_eq, List.tail_cons, List.map_cons,
      List.foldr_cons, List.sum_cons] at ih' ⊢
    rw [ih', hx x List.mem_cons_self d]
    rfl

/-- The mirror's uses of a variable in an encoded term. -/
theorem uses_eq (t : Term) (d : ℕ) :
    «Prover.uses» (encTerm t) (leaf d) = leaf (Internal.uses t d) := by
  simp only [«Prover.uses», template, Internal.uses, elim_eq_para]
  refine para_enc _ _ (fun (v : Tree → Tree) (w : ℕ → ℕ) ↦ ∀ d, v (leaf d) = leaf (w d))
    «Prover.usesStep» _ (fun l v xs hx d ↦ ?_) t d
  change «Prover.usesStep» (encTerm (RoseTree.node l (xs.map Prod.fst))) _ (leaf d) = _
  have hs := ufSum_eq v d xs hx
  have hs1 := ufSum_eq v (d + 1) xs hx
  simp only [List.map_map, Function.comp_def]
  cases l with
  | var i =>
    mirror_simp [«Prover.usesStep», labelData, mArgs_eq, label_encTerm, mD_eq]
    by_cases h : i = d <;> simp [h]
  | natRec | listRec =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, xs⟩⟩⟩⟩ <;>
      simp only [List.map_cons, List.map_nil] at hs <;>
      mirror_simp [«Prover.usesStep», labelData, hs, mArgs_eq, label_encTerm,
        beq_iff_eq, Nat.reduceEqDiff, ufAt_eq, hx]
    all_goals rw [hx x0 (by simp), hx x1 (by simp), hx x2 (by simp), mul_leaf, add_leaf, add_leaf]
  | roseRec c =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩ <;>
      simp only [List.map_cons, List.map_nil] at hs <;>
      mirror_simp [«Prover.usesStep», labelData, hs, mArgs_eq, label_encTerm,
        beq_iff_eq, Nat.reduceEqDiff, ufAt_eq, hx]
    all_goals exact hx _ (by simp) d
  | _ =>
    mirror_simp [«Prover.usesStep», labelData, hs, hs1, mArgs_eq, label_encTerm, mD_eq]

/-- The mirror's child of an encoded node whose reduction can enable a rule at its root. -/
theorem headChild_eq (l : Internal.Label) (ts : List Term) :
    «Prover.headChild» (encTerm (RoseTree.node l ts)) =
      encOpt ((Internal.headChild l ts).map leaf) := by
  cases l <;> rcases ts with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, ts⟩⟩⟩⟩ <;>
    mirror_simp [«Prover.headChild», Internal.headChild, labelData, mIs_eq, some_eq,
      none_eq, beq_iff_eq, Nat.reduceEqDiff]

/-- The mirror's test that the open normal form leaves a node's child of an index in place. -/
@[simp] theorem keepsFold_eq (l : Internal.Label) (i : ℕ) :
    «Prover.keepsFold» (leaf (labelData l).1) (leaf i) =
      ofBool (Internal.keepsFold l i) := by
  cases l <;> mirror_simp [«Prover.keepsFold», Internal.keepsFold, labelData] <;> rfl

/-- The mirror's test that the weak normal form leaves a node's child of an index in place. -/
@[simp] theorem keepsWeak_eq (l : Internal.Label) (i : ℕ) :
    «Prover.keepsWeak» (leaf (labelData l).1) (leaf i) =
      ofBool (Internal.keepsWeak l i) := by
  cases l <;> mirror_simp [«Prover.keepsWeak», «Prover.keepsFold»,
    Internal.keepsWeak, labelData] <;> rfl

/-- A depth of reduction as the mirror's number: the weak head normal form zero, the weak normal
form one, the open normal form two and the normal form three. -/
def encDepth : Internal.Depth → ℕ
  | .head => 0
  | .weak => 1
  | .open => 2
  | .full => 3

/-- The mirror's reduction and a reduction are related when they agree at every depth, context,
encoded hypotheses and encoded term. -/
def ERel (v : Tree → List Tree → List Tree → Tree → Tree) (w : Internal.Reduction) : Prop :=
  ∀ dp Γ Φ t, v (leaf (encDepth dp)) Γ (Φ.map encTerm) (encTerm t) =
    encOpt ((w dp Γ Φ t).map encTDB)

/-- The mirror's rewriting at the root followed by a reduction, at related rules and
reductions. -/
theorem atRoot_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (rec' : Tree → List Tree → List Tree → Tree → Tree)
    (rec : Internal.Reduction) (hrec : ERel rec' rec) (dp : Internal.Depth) (t₁ : Term)
    (d₁ : Deriv × Bool) :
    «Prover.atRoot» (encGlobals G) (E.toList.map encEntry) (leaf n) rs' rec' Γ
        (Φ.map encTerm) (leaf (encDepth dp)) (encTerm t₁) (encDB d₁) =
      encOpt ((Internal.atRoot G E n rs rec Γ Φ dp t₁ d₁).map encTDB) := by
  simp only [«Prover.atRoot», template, Internal.atRoot, rootRewrite_eq G E n Γ Φ rs' rs hrs,
    isSome_eq]
  rcases Internal.rootRewrite G E n rs Γ Φ t₁ with _ | ⟨t₂, dr⟩
  · rfl
  · have h2 : «Language.pr» (encDeriv dr) (leaf 1) = encDB (dr, true) := rfl
    simp only [Option.map_some, Option.isSome_some, ofBool_true, label_leaf, ne_eq,
      one_ne_zero, not_false_eq_true, ↓reduceIte, tmpl_fromMaybe_eq, Option.getD_some,
      p1_encTD,
      p2_encTD, hrec dp Γ Φ t₂, mapO_eq, Option.map_map, h2]
    rcases rec dp Γ Φ t₂ with _ | ⟨t₃, d₃⟩
    · rfl
    · simp only [Option.map_some, Function.comp_apply, p1_encTDB, p2_encTDB, dTrans_eq]
      rfl

/-- A label's position is the application's exactly at the application. -/
theorem labelData_eq_app (l : Internal.Label) : (labelData l).1 = 6 ↔ l = .app := by
  cases l <;> simp [labelData]

/-- A label's position is the abstraction's exactly at an abstraction. -/
theorem labelData_eq_lam (l : Internal.Label) : (labelData l).1 = 5 ↔ ∃ a, l = .lam a := by
  cases l <;> simp [labelData]

/-- The mirror's step of the weak head normal form, at related rules and reductions of the
subterms. -/
theorem headStep_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (rec' : Tree → List Tree → List Tree → Tree → Tree)
    (rec : Internal.Reduction) (hrec : ERel rec' rec) (t : Term) :
    «Prover.headStep» (encGlobals G) (E.toList.map encEntry) (leaf n) rs' rec' Γ
        (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.headStep G E n rs rec Γ Φ t).map encTDB) := by
  have h0 : ∀ Γ Φ t, rec' (leaf 0) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((rec .head Γ Φ t).map encTDB) := hrec .head
  have h1 : ∀ Γ Φ t, rec' (leaf 1) Γ (Φ.map encTerm) (encTerm t) =
      encOpt ((rec .weak Γ Φ t).map encTDB) := hrec .weak
  have hA : ∀ t₁ d₁, «Prover.atRoot» (encGlobals G) (E.toList.map encEntry) (leaf n)
      rs' rec' Γ (Φ.map encTerm) (leaf 0) (encTerm t₁) (encDB d₁) =
      encOpt ((Internal.atRoot G E n rs rec Γ Φ .head t₁ d₁).map encTDB) :=
    atRoot_eq G E n Γ Φ rs' rs hrs rec' rec hrec .head
  obtain ⟨l, ts, rfl⟩ : ∃ l ts, t = RoseTree.node l ts :=
    ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩
  by_cases happ : (labelData l).1 = 6 ∧ ts.length = 2
  · obtain ⟨hl, h2⟩ := happ
    obtain rfl := (labelData_eq_app l).mp hl
    match ts, h2 with
    | [f, u], _ =>
      simp only [«Prover.headStep», template, Internal.headStep]
      mirror_simp [mIs_eq, labelData, mArg_eq, h0]
      rcases rec .head Γ Φ f with _ | ⟨f', df⟩
      · rfl
      have hL : ∀ (u' : Term) (du : Deriv × Bool), «Prover.atRoot» (encGlobals G)
          (E.toList.map encEntry) (leaf n) rs' rec' Γ (Φ.map encTerm) (leaf 0)
          («Language.app» (encTerm f') (encTerm u'))
          («Prover.dCong» («Theory.l2» (encDB df) (encDB du))) =
          encOpt ((Internal.atRoot G E n rs rec Γ Φ .head (Term.app f' u')
            (Internal.dCong [df, du])).map encTDB) := fun u' du ↦ by
        rw [mApp_eq, ← hA]
        exact congrArg _ (dCong_eq [df, du])
      simp only [Option.map_some, Option.elim_some, p1_encTDB, p2_encTDB]
      obtain ⟨l', ts', rfl⟩ : ∃ l ts, f' = RoseTree.node l ts :=
        ⟨f'.label, f'.children, (RoseTree.node_label_children f').symm⟩
      by_cases hlam : (labelData l').1 = 5 ∧ ts'.length = 1
      · obtain ⟨hl', h1'⟩ := hlam
        obtain ⟨a, rfl⟩ := (labelData_eq_lam l').mp hl'
        match ts', h1' with
        | [b], _ =>
          mirror_simp [mIs_eq, labelData, mArg_eq, uses_eq, Option.bind_eq_bind]
          by_cases hu : Internal.uses b 0 < 2
          · have hp : «Language.pr» (encTerm u) «Prover.dRefl» =
                encTDB (u, Internal.dRefl) := rfl
            simp only [hu, decide_true, ↓reduceIte, hp, some_eq, bindO_eq, Option.elim_some,
              p1_encTDB, p2_encTDB, hL]
          · simp only [hu, decide_false, Bool.false_eq_true, ↓reduceIte, h1, bindO_eq]
            rcases rec .weak Γ Φ u with _ | ⟨u', du⟩
            · rfl
            · simp only [Option.map_some, Option.elim_some, p1_encTDB, p2_encTDB, hL,
                Option.bind_some]
      · mirror_simp [mIs_eq, Bool.and_eq_true, beq_iff_eq, hlam, Option.bind_eq_bind]
        split
        · exact absurd ⟨(labelData_eq_lam _).mpr ⟨_, rfl⟩, rfl⟩ hlam
        · rcases rec .head Γ Φ u with _ | ⟨u', du⟩
          · rfl
          · simp only [Option.map_some, Option.elim_some, p1_encTDB, p2_encTDB, hL,
              Option.bind_some]
  · generalize hM : «Prover.headStep» (encGlobals G) (E.toList.map encEntry) (leaf n)
      rs' rec' Γ (Φ.map encTerm) (encTerm (RoseTree.node l ts)) = M
    simp only [Internal.headStep, RoseTree.label_node, RoseTree.children_node]
    split
    · exact absurd ⟨rfl, rfl⟩ happ
    subst hM
    simp only [«Prover.headStep», template]
    mirror_simp [mIs_eq, Bool.and_eq_true, beq_iff_eq, happ, rootRewrite_eq G E n Γ Φ rs' rs hrs]
    rcases Internal.rootRewrite G E n rs Γ Φ (RoseTree.node l ts) with _ | ⟨t₁, dr⟩
    · mirror_simp [headChild_eq]
      rcases Internal.headChild l ts with _ | i
      · rfl
      mirror_simp [mArgs_eq, Option.bind_eq_bind]
      rcases ts[i]? with _ | c
      · rfl
      mirror_simp [h0]
      rcases rec .head Γ Φ c with _ | ⟨c', dd, _ | _⟩
      · rfl
      · rfl
      have hn : RoseTree.node (labelData l).1
          (Const.child (encTerm (RoseTree.node l ts)) (leaf 0) ::
            (ts.map encTerm).set i (encTerm c')) = encTerm (RoseTree.node l (ts.set i c')) := by
        simp [encTerm_node, child_node, List.map_set]
      have hd : «Prover.dCong» ((List.range ts.length).map fun j ↦
          if j = i then encDB (dd, true) else «Prover.dRefl») =
          encDB (Internal.dCong ((List.range ts.length).map fun j ↦
            if j = i then (dd, true) else Internal.dRefl)) := by
        rw [← dCong_eq, List.map_map]
        exact congrArg _ (List.map_congr_left fun j _ ↦ by
          simp only [Function.comp_apply]
          split <;> rfl)
      mirror_simp [p1_encTDB, p2_encTDB, p2_encDB, ofBool_true, setAt_eq, label_encTerm, hn,
        Nat.reduceBNe]
      rw [← hA, ← hd]
      rfl
    · have h2 : «Language.pr» (encDeriv dr) (leaf 1) = encDB (dr, true) := rfl
      mirror_simp [p1_encTD, p2_encTD, h0, h2]
      rcases rec .head Γ Φ t₁ with _ | ⟨t₂, d₂⟩
      · rfl
      · simp only [Option.map_some, p1_encTDB, p2_encTDB, dTrans_eq]
        rfl

/-- The mirror's trees of the images of a list's positions, each present, where the image of a
position is that of the element there. -/
theorem allSomeT_range {α : Type} (xs : List α) (F : ℕ → Tree) (f : α → Option Tree)
    (h : ∀ i (hi : i < xs.length), F i = encOpt (f xs[i])) :
    «Base.allSomeT» ((List.range xs.length).map F) =
      encOpt ((xs.mapM f).map (RoseTree.node 0)) := by
  have hm : (List.range xs.length).map F = xs.map fun x ↦ encOpt (f x) :=
    List.ext_getElem (by simp) fun i h1 _ ↦ by
      simp only [List.getElem_map, List.getElem_range]
      exact h i (by simpa using h1)
  rw [hm, allSomeT_eq]

/-- The mirror's trees of the images of a list's positions, each present, where the image of a
position is that of the element there with the position. -/
theorem allSomeT_range_zipIdx {α : Type} (xs : List α) (F : ℕ → Tree) (f : α × ℕ → Option Tree)
    (h : ∀ i (hi : i < xs.length), F i = encOpt (f (xs[i], i))) :
    «Base.allSomeT» ((List.range xs.length).map F) =
      encOpt ((xs.zipIdx.mapM f).map (RoseTree.node 0)) := by
  rw [← List.length_zipIdx (l := xs) (i := 0)]
  exact allSomeT_range _ F f fun i hi ↦ by
    rw [List.getElem_zipIdx, zero_add]
    exact h i (by simpa using hi)

/-- An element of the images of a list at a position within it. -/
theorem getD_map_of_lt {α : Type} (xs : List α) (g : α → Tree) (i : ℕ) (hi : i < xs.length)
    {d : Tree} : (xs.map g).getD i d = g xs[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- The mirror's binding of the encoded list of an optional list, at a continuation related to a
continuation of the list. -/
theorem bindO_list {α : Type} (o : Option (List α)) (e : α → Tree) (K : Tree → Tree)
    (L : List α → Option (Term × Deriv × Bool))
    (h : ∀ cs, K (RoseTree.node 0 (cs.map e)) = encOpt ((L cs).map encTDB)) :
    «Base.bindO» (encOpt ((o.map (List.map e)).map (RoseTree.node 0))) K =
      encOpt ((o.bind L).map encTDB) := by
  cases o
  · rfl
  · exact h _

/-- The mirror's reduction past a weak head normal form, to a depth past it, at related rules and
reductions of the subterms. -/
theorem deepStep_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (rec' : Tree → List Tree → List Tree → Tree → Tree)
    (rec : Internal.Reduction) (hrec : ERel rec' rec) (dp : Internal.Depth) (hdp : dp ≠ .head)
    (w : Term) (dw : Deriv × Bool) :
    «Prover.deepStep» (encGlobals G) (E.toList.map encEntry) (leaf n) rs' rec'
        (leaf (encDepth dp)) Γ (Φ.map encTerm) (encTerm w) (encDB dw) =
      encOpt ((Internal.deepStep G E n rs rec dp Γ Φ w dw).map encTDB) := by
  have hC : ∀ cs : List (Term × Deriv × Bool), «Prover.dCong»
      (cs.map fun x ↦ encDB x.2) = encDB (Internal.dCong (cs.map Prod.snd)) := fun cs ↦ by
    rw [← dCong_eq, List.map_map]
    rfl
  obtain ⟨l, ts, rfl⟩ : ∃ l ts, w = RoseTree.node l ts :=
    ⟨w.label, w.children, (RoseTree.node_label_children w).symm⟩
  cases dp with
  | head => exact absurd rfl hdp
  | weak =>
    simp only [«Prover.deepStep», template, Internal.deepStep, encDepth]
    mirror_simp [label_encTerm, mArgs_eq, Option.bind_eq_bind]
    rw [allSomeT_range_zipIdx ts _ (fun x ↦ (if Internal.keepsWeak l x.2 = true then
      some (x.1, Internal.dRefl) else rec .weak Γ Φ x.1).map encTDB) fun i hi ↦ by
        rw [keepsWeak_eq, getD_map_of_lt _ _ i hi]
        cases Internal.keepsWeak l i
        · exact hrec .weak Γ Φ ts[i]
        · rfl, Infer.mapM_map_option]
    refine bindO_list _ encTDB _ _ fun cs ↦ ?_
    have hA := atRoot_eq G E n Γ Φ rs' rs hrs rec' rec hrec .weak
    mirror_simp [RoseTree.children_node, marked_eq, rebuild_eq, p2_encTDB, hC, dTrans_eq]
    cases cs.any fun x ↦ x.2.2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [↓reduceIte]
      exact hA _ _
  | «open» =>
    simp only [«Prover.deepStep», template, Internal.deepStep, encDepth]
    mirror_simp [label_encTerm, mArgs_eq, childCtxs_eq, Option.bind_eq_bind]
    rcases Internal.childCtxs G n l ts Γ Φ with _ | Γs
    · rfl
    mirror_simp [zipTs_eq, List.zip_map]
    rw [allSomeT_range_zipIdx (Γs.zip ts) _ (fun x ↦ (if Internal.keepsFold l x.2 = true then
      some (x.1.2, Internal.dRefl) else rec .open x.1.1.1 x.1.1.2 x.1.2).map encTDB) fun i hi ↦ by
        rw [keepsFold_eq, getD_map_of_lt _ _ i hi]
        cases Internal.keepsFold l i
        · mirror_simp [p1_eq, p2_eq, encCtx, Prod.map]
          exact hrec .open _ _ _
        · rfl, Infer.mapM_map_option]
    refine bindO_list _ encTDB _ _ fun cs ↦ ?_
    have hA := atRoot_eq G E n Γ Φ rs' rs hrs rec' rec hrec .open
    mirror_simp [RoseTree.children_node, marked_eq, rebuild_eq, p2_encTDB, hC, dTrans_eq]
    cases cs.any fun x ↦ x.2.2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [↓reduceIte]
      exact hA _ _
  | full =>
    have h3 : ∀ Γ Φ t, rec' (leaf 3) Γ (Φ.map encTerm) (encTerm t) =
        encOpt ((rec .full Γ Φ t).map encTDB) := hrec .full
    have h2 : ∀ dr : Deriv, «Language.pr» (encDeriv dr) (leaf 1) = encDB (dr, true) :=
      fun _ ↦ rfl
    simp only [«Prover.deepStep», template, Internal.deepStep, encDepth]
    mirror_simp [label_encTerm, mArgs_eq, childCtxs_eq, Option.bind_eq_bind]
    rcases Internal.childCtxs G n l ts Γ Φ with _ | Γs
    · rfl
    mirror_simp [zipTs_eq, List.zip_map]
    rw [allSomeT_range (Γs.zip ts) _ (fun x ↦ (rec .full x.1.1 x.1.2 x.2).map encTDB) fun i hi ↦ by
        rw [getD_map_of_lt _ _ i hi]
        mirror_simp [p1_eq, p2_eq, encCtx, Prod.map]
        exact hrec .full _ _ _, Infer.mapM_map_option]
    refine bindO_list _ encTDB _ _ fun cs ↦ ?_
    mirror_simp [RoseTree.children_node, rebuild_eq, p2_encTDB, hC,
      rootRewrite_eq G E n Γ Φ rs' rs hrs]
    rcases Internal.rootRewrite G E n rs Γ Φ (RoseTree.node l (cs.map Prod.fst)) with _ | ⟨t₂, dr⟩
    · simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, dTrans_eq]
      rfl
    · mirror_simp [p1_encTD, p2_encTD, h2, h3]
      rcases rec .full Γ Φ t₂ with _ | ⟨t₃, d₃⟩
      · rfl
      · simp only [Option.map_some, p1_encTDB, p2_encTDB, dTrans_eq]
        rfl

/-- The mirror's step of the reduction to a depth, at related rules and reductions of the
subterms. -/
theorem evalStep_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (rec' : Tree → List Tree → List Tree → Tree → Tree)
    (rec : Internal.Reduction) (hrec : ERel rec' rec) :
    ERel («Prover.evalStep» (encGlobals G) (E.toList.map encEntry) (leaf n) rs' rec')
      (Internal.evalStep G E n rs rec) := by
  intro dp Γ Φ t
  simp only [«Prover.evalStep», template, Internal.evalStep,
    headStep_eq G E n Γ Φ rs' rs hrs rec' rec hrec, bindO_eq, Option.bind_eq_bind]
  rcases Internal.headStep G E n rs rec Γ Φ t with _ | ⟨w, dw⟩
  · rfl
  cases dp with
  | head => rfl
  | weak => exact deepStep_eq G E n Γ Φ rs' rs hrs rec' rec hrec .weak nofun w dw
  | «open» => exact deepStep_eq G E n Γ Φ rs' rs hrs rec' rec hrec .open nofun w dw
  | full => exact deepStep_eq G E n Γ Φ rs' rs hrs rec' rec hrec .full nofun w dw

/-- The mirror's reduction to a depth within a depth of fuel, at related rules. -/
theorem eval_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) :
    ERel («Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (leaf fuel))
      (Internal.eval G E n rs fuel) := by
  simp only [«Prover.eval», template, iter_leaf, Internal.eval]
  exact Nat.rec (fun _ _ _ _ ↦ rfl)
    (fun k ih ↦ by rw [Nat.repeat]; exact evalStep_eq G E n rs' rs hrs _ _ ih) fuel

/-- The mirror's normal form reached through weak head normal forms, at related rules. -/
theorem normalizeW_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree)))
    (rs : List NormRule) (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) :
    NRel («Prover.normalizeW» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (leaf fuel))
      (Internal.normalizeW G E n rs fuel) :=
  eval_eq G E n rs' rs hrs fuel .full

/-- The mirror's proof of an equation by normalizing both sides, weak head normal forms first,
to one term. -/
theorem byNormW_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t u : Term) :
    «Prover.byNormW» (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf fuel)
        Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((Internal.byNormW G E n rs fuel Γ Φ t u).map encDeriv) := by
  rw [«Prover.byNormW», joinBy_eq _ _ (normalizeW_eq G E n rs' rs hrs fuel)]
  rfl

/-! Provers of equations. -/

/-- The mirror's prover and a prover are related when they agree at every context, encoded
hypotheses and encoded sides. -/
def PRel (v : List Tree → List Tree → Tree → Tree → Tree) (w : Internal.Prover) : Prop :=
  ∀ Γ Φ t u, v Γ (Φ.map encTerm) (encTerm t) (encTerm u) = encOpt ((w Γ Φ t u).map encDeriv)

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
      encOpt ((p Γ Φ t u).map encDeriv) := hp
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
      encOpt ((p Γ Φ t u).map encDeriv) := hp
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
      encOpt ((p₀ Γ Φ t u).map encDeriv) := hp₀
  have hp₁' : ∀ Γ Φ t u, p₁' Γ (Φ.map encTerm) (encTerm t) (encTerm u) =
      encOpt ((p₁ Γ Φ t u).map encDeriv) := hp₁
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
    (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) (Γ : List Tree) (t u : Term) :
    «Prover.byRoseInd» (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn)
        (leaf kl) (leaf kc) (encTerm s) rs' (leaf fuel) Γ (encTerm t) (encTerm u) =
      encOpt ((Internal.byRoseInd G E n kn kl kc s rs fuel Γ t u).map encDeriv) := by
  have hB : ∀ Γ t u, «Prover.byNorm» (encGlobals G) (E.toList.map encEntry) (leaf n)
      rs' (leaf fuel) Γ [] (encTerm t) (encTerm u) =
      encOpt ((Internal.byNorm G E n rs fuel Γ [] t u).map encDeriv) :=
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
      encOpt ((p Γ Φ t u).map encDeriv) := hp
  intro Γ Φ t u
  rcases Γ with _ | ⟨r, _ | ⟨r', Γ'⟩⟩ <;>
    simp only [«Prover.byRoseIndHyp», template, Internal.byRoseIndHyp]
  · rfl
  · mirror_simp [roseLabel_eq, Theory.mirror_list, «Theory.l3»,
      «Theory.l2», Option.bind_eq_bind]
    rcases Internal.roseParts r with _ | ⟨a, f⟩
    · rfl
    have h := hp' [list r, a] [Internal.roseHyp kl kc (Term.eq t u)]
      (Internal.roseNodeAt kn r a t) (Internal.roseNodeAt kn r a u)
    simp only [List.map_cons, List.map_nil] at h
    ind_simp [roseNodeAt_eq, roseHyp_eq, mEq_eq, h]
    simp only [Option.map_eq_bind, Function.comp_def]
  · mirror_simp [beq_iff_eq, Nat.reduceEqDiff, none_eq]

end GebTests.Prototypes.FreeTopos.Agreement.Prove

end
