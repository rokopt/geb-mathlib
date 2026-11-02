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

The mirror's reduction to a depth is that of {name}`Geb.FreeTopos.Internal.evalFast`: it reduces
under the hypotheses as stated with the number of variables past which they are weakened, by a
rewriting at the root that tries only the rules of the key of a term's root label and compares a
term with an equation among the hypotheses by its left side's renaming, folded once. Its agreement
with {name}`Geb.FreeTopos.Internal.evalK` at a rewriting at the root under the hypotheses
weakened, composed with {name}`Geb.FreeTopos.Internal.evalK_eq`, is the agreement with the
reduction as it is defined.

## Main definitions

* {lit}`encDB`, {lit}`encTDB`, {lit}`encOT`, {lit}`encDepth` — a rewriting's derivation with
  its mark, a term with it, an optional term of an assignment, and a depth of reduction.
* {lit}`MRel`, {lit}`RRel`, {lit}`NRel`, {lit}`ERel`, {lit}`PRel` — the relations of the
  mirror's matchings, rules, normalizations, reductions to a depth and provers to the prover's.
* {lit}`WRel`, {lit}`EKRel` — the relations of the mirror's rewritings at the root and reductions
  under weakened hypotheses to the prover's.
* {lit}`encPH` — an equation among the hypotheses as the mirror prepares it.

## Main statements

* {lit}`rootRewriteK_eq` — the rewriting at the root by the index of the rules and the prepared
  hypotheses is the rewriting by the rules under the hypotheses weakened.
* {lit}`evalK_eq`, {lit}`eval_eq` — the reductions to a depth, under weakened hypotheses and as
  defined, agree.

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
@[template] theorem bindP_def : «Prover.bindP» = «Base.bindO» := by
  funext a b
  simp only [«Prover.bindP», «Base.bindO», «Prelude.isSome», «Prelude.get»,
    children_eq, lcase_children_head]
  rfl

@[template, inherit_doc bindP_def] theorem bindAA_def : «Prover.bindAA» = «Base.bindO» := by
  funext a b
  simp only [«Prover.bindAA», «Base.bindO», «Prelude.isSome», «Prelude.get»,
    children_eq, lcase_children_head]
  rfl

@[template, inherit_doc bindP_def] theorem bindAP_def : «Prover.bindAP» = «Base.bindO» := by
  funext a b
  simp only [«Prover.bindAP», «Base.bindO», «Prelude.isSome», «Prelude.get»,
    children_eq, lcase_children_head]
  rfl

@[template, inherit_doc bindP_def] theorem bindHP_def : «Prover.bindHP» = «Base.bindO» := by
  funext a b
  simp only [«Prover.bindHP», «Base.bindO», «Prelude.isSome», «Prelude.get»,
    children_eq, lcase_children_head]
  rfl

@[template, inherit_doc bindP_def] theorem bindNT_def : «Prover.bindNT» = «Base.bindO» := by
  funext a b
  simp only [«Prover.bindNT», «Base.bindO», «Prelude.isSome», «Prelude.get»,
    children_eq, lcase_children_head]
  rfl

@[template, inherit_doc bindP_def] theorem bindNN_def : «Prover.bindNN» = «Base.bindO» := by
  funext a b
  simp only [«Prover.bindNN», «Base.bindO», «Prelude.isSome», «Prelude.get»,
    children_eq, lcase_children_head]
  rfl

@[template, inherit_doc bindP_def] theorem bindTN_def : «Prover.bindTN» = «Base.bindO» := rfl

@[template, inherit_doc bindP_def] theorem bindSN_def : «Prover.bindSN» = «Base.bindO» := by
  funext a b
  simp only [«Prover.bindSN», «Base.bindO», «Prelude.isSome», «Prelude.get»,
    children_eq, lcase_children_head]
  rfl

@[template, inherit_doc bindP_def] theorem bindLN_def : «Prover.bindLN» = «Base.bindO» := by
  funext a b
  simp only [«Prover.bindLN», «Base.bindO», «Prelude.isSome», «Prelude.get»,
    children_eq, lcase_children_head]
  rfl

@[template, inherit_doc bindP_def] theorem bindHT_def : «Prover.bindHT» = «Base.bindO» := by
  funext a b
  simp only [«Prover.bindHT», «Base.bindO», «Prelude.isSome», «Prelude.get»,
    children_eq, lcase_children_head]
  rfl

@[template, inherit_doc bindP_def] theorem mapTP_def : «Prover.mapTP» = «Base.mapO» := rfl

@[template, inherit_doc bindP_def] theorem mapNN_def : «Prover.mapNN» = «Base.mapO» := by
  funext a b
  simp only [«Prover.mapNN», «Base.mapO», «Prelude.isSome», «Prelude.get»,
    children_eq, lcase_children_head]
  rfl

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
    all_goals rw [hx x0 (by simp), hx x1 (by simp), mul_leaf, add_leaf]
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

/-! The rewriting at the root under weakened hypotheses. -/

/-- The mirror's key of an encoded term's root label. -/
@[simp] theorem rootKey_eq (t : Term) : «Prover.rootKey» (encTerm t) = leaf t.label.rootKey := by
  obtain ⟨l, cs, rfl⟩ := exists_node t
  cases l <;> mirror_simp [«Prover.rootKey», label_encTerm, mD_eq, labelData,
    Internal.Label.rootKey]

/-- The mirror's key of the labels at which an encoded pattern may match. -/
@[simp] theorem patternKey_eq (p : Term) :
    «Prover.patternKey» (encTerm p) = encOpt (p.label.patternKey?.map leaf) := by
  obtain ⟨l, cs, rfl⟩ := exists_node p
  cases l <;> mirror_simp [«Prover.patternKey», label_encTerm, labelData, none_eq, some_eq,
    Internal.Label.patternKey?, rootKey_eq]

/-- The mirror's key of the labels at which a rule of the checker may rewrite. -/
@[simp] theorem ruleKey_eq (l : Internal.Rule) :
    «Prover.ruleKey» (leaf (ruleData l).1) = encOpt (l.rootKey?.map leaf) := by
  cases l <;> mirror_simp [«Prover.ruleKey», ruleData, Internal.Rule.rootKey?, none_eq, some_eq]

/-- The mirror's key of the labels at which a rule related to a rule of the normalizer may
rewrite. -/
theorem nrKey_eq (r' : Tree × (Tree → Tree → List Tree → Tree)) (r : NormRule) (h : RRel r' r) :
    «Prover.nrKey» (E.toList.map encEntry) r' = encOpt ((r.rootKey? E).map leaf) := by
  cases r
  case thmAt j θ root m k =>
    obtain ⟨p, hp, h1, -⟩ := h
    simp only [«Prover.nrKey», template, h1]
    mirror_simp [List.getD_cons_zero, List.getD_cons_succ, Internal.NormRule.rootKey?,
      patternKey_eq, hp]
  case thm j θ =>
    simp only [RRel] at h
    simp only [«Prover.nrKey», template, h, encRule]
    mirror_simp [List.getD_cons_zero, List.getD_cons_succ, Array.getElem?_toList,
      entryLanguage_eq, Internal.NormRule.rootKey?]
    rcases E[j]? with _ | (a | s)
    · rfl
    · mirror_simp [entryLanguage_eq, Internal.Entry.language?, thConcl_eq, eqParts_eq]
      rcases Internal.eqParts a.concl with _ | ⟨l, r⟩ <;>
        mirror_simp [p1_eq, patternKey_eq, none_eq]
    · mirror_simp [entryLanguage_eq, Internal.Entry.language?, none_eq]
  case rule l =>
    simp only [RRel] at h
    simp only [«Prover.nrKey», template, h, encRule]
    mirror_simp [List.getD_cons_zero, Internal.NormRule.rootKey?, ruleKey_eq]
  all_goals
    simp only [RRel] at h
    simp only [«Prover.nrKey», template, h, encRule]
    mirror_simp [List.getD_cons_zero, Internal.NormRule.rootKey?, none_eq, some_eq]

/-- The mirror's test that a rule of a key, where it has one, may rewrite at a label of a key. -/
@[simp] theorem keyFits_eq (k : ℕ) (o : Option ℕ) :
    «Prover.keyFits» (leaf k) (encOpt (o.map leaf)) = ofBool (Internal.keyFits k o) := by
  cases o
  · mirror_simp [«Prover.keyFits», Internal.keyFits, ofBool_true]
  · mirror_simp [«Prover.keyFits», Internal.keyFits]

/-- The mirror's test of a key reads only the key's label. -/
theorem keyFits_label (x m : Tree) : «Prover.keyFits» x m = «Prover.keyFits» (leaf x.label) m :=
  rfl

/-- The mirror's rules of a list that may rewrite at a label of a key, in order. -/
theorem bucketOf_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (x : Tree) :
    «Prover.bucketOf» (E.toList.map encEntry) rs' x =
      rs'.filter fun r' ↦
        decide ((«Prover.keyFits» x («Prover.nrKey» (E.toList.map encEntry) r')).label ≠ 0) := by
  simp only [«Prover.bucketOf», foldr_eq]
  exact rs'.rec rfl fun r' rs' ih ↦ by
    rw [List.foldr_cons, ih, List.filter_cons]
    split <;> simp_all

/-- Each key of a rule of a list is, up to its label, among the mirror's keys of the list. -/
theorem ruleKeys_mem (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) :
    ∀ r' ∈ rs', («Prover.nrKey» (E.toList.map encEntry) r').label = 1 →
      ∃ x ∈ «Prover.ruleKeys» (E.toList.map encEntry) rs',
        x.label = («Prelude.get» («Prover.nrKey» (E.toList.map encEntry) r')).label := by
  simp only [«Prover.ruleKeys», foldr_eq]
  refine rs'.rec (fun _ h ↦ absurd h List.not_mem_nil) fun r rs' ih r' hr h1 ↦ ?_
  simp only [List.foldr_cons]
  generalize hK : List.foldr _ [] rs' = K at ih ⊢
  have hany : ∀ g, «Base.anyT» (fun x ↦ Const.eq x g) K =
      ofBool (K.any fun x ↦ x.label == g.label) :=
    fun g ↦ anyT_eq _ _ K fun _ _ ↦ rfl
  have hsub : ∀ x ∈ K, x ∈ (if («Prelude.and» («Prelude.isSome» («Prover.nrKey»
      (E.toList.map encEntry) r)) («Base.not» («Base.anyT» (fun x ↦ Const.eq x
      («Prelude.get» («Prover.nrKey» (E.toList.map encEntry) r))) K))).label ≠ 0 then
      «Prelude.get» («Prover.nrKey» (E.toList.map encEntry) r) :: K else K) := fun x hx ↦ by
    split
    · exact List.mem_cons_of_mem _ hx
    · exact hx
  rcases List.mem_cons.mp hr with rfl | hr
  · by_cases hn : (K.any fun x ↦ x.label == («Prelude.get»
        («Prover.nrKey» (E.toList.map encEntry) r')).label) = true
    · obtain ⟨x, hx, hl⟩ := List.any_eq_true.mp hn
      exact ⟨x, hsub x hx, beq_iff_eq.mp hl⟩
    · refine ⟨_, ?_, rfl⟩
      have hs : «Prelude.isSome» («Prover.nrKey» (E.toList.map encEntry) r') = ofBool true := by
        simp [«Prelude.isSome», Const.eq, h1]
      rw [hany, hs, Bool.eq_false_iff.mpr hn, not_eq, and_eq]
      simp
  · obtain ⟨x, hx, hl⟩ := ih r' hr h1
    exact ⟨x, hsub x hx, hl⟩

/-- The mirror's index of rules gives at a key the rules that may rewrite at a label of it. -/
theorem ruleBucket_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (x : Tree) :
    «Prover.ruleBucket» («Prover.indexRules» (E.toList.map encEntry) rs') x =
      «Prover.bucketOf» (E.toList.map encEntry) rs' x := by
  have hb : ∀ y, y.label = x.label → «Prover.bucketOf» (E.toList.map encEntry) rs' y =
      «Prover.bucketOf» (E.toList.map encEntry) rs' x := fun y hy ↦ by
    rw [bucketOf_eq, bucketOf_eq]
    congr 1
    funext r'
    rw [keyFits_label y, keyFits_label x, hy]
  have hK := ruleKeys_mem E rs'
  simp only [«Prover.ruleBucket», «Prover.indexRules», foldr_eq]
  generalize «Prover.ruleKeys» (E.toList.map encEntry) rs' = K at hK
  by_cases hx : ∃ y ∈ K, y.label = x.label
  · revert hx
    refine K.rec (fun ⟨_, h, _⟩ ↦ absurd h List.not_mem_nil) fun y K ih hx ↦ ?_
    simp only [List.foldr_cons, Const.eq, label_ne_zero, ofBool_bne] at ih ⊢
    split
    · rename_i h
      exact hb y (beq_iff_eq.mp h)
    · rename_i h
      obtain ⟨z, hz, hl⟩ := hx
      rcases List.mem_cons.mp hz with rfl | hz
      · exact absurd (beq_iff_eq.mpr hl) h
      · exact ih ⟨z, hz, hl⟩
  · have hf : ∀ K' : List Tree, (∀ y ∈ K', y.label ≠ x.label) →
        List.foldr (fun b acc ↦ if (Const.eq b.1 x).label ≠ 0 then b.2 else acc)
          (List.foldr (fun r acc ↦ if («Prelude.isSome» («Prover.nrKey»
            (E.toList.map encEntry) r)).label ≠ 0 then acc else r :: acc) [] rs')
          (List.foldr (fun k acc ↦ (k, «Prover.bucketOf» (E.toList.map encEntry) rs' k) :: acc)
            [] K') =
        List.foldr (fun r acc ↦ if («Prelude.isSome» («Prover.nrKey»
          (E.toList.map encEntry) r)).label ≠ 0 then acc else r :: acc) [] rs' :=
      fun K' ↦ K'.rec (fun _ ↦ rfl) fun y K' ih h ↦ by
        simp only [List.foldr_cons, Const.eq, label_ne_zero, ofBool_bne,
          beq_iff_eq, h y List.mem_cons_self, ↓reduceIte] at ih ⊢
        exact ih fun z hz ↦ h z (List.mem_cons_of_mem _ hz)
    rw [hf K fun y hy hl ↦ hx ⟨y, hy, hl⟩, bucketOf_eq]
    have hd : ∀ rs'' : List (Tree × (Tree → Tree → List Tree → Tree)),
        List.foldr (fun r acc ↦ if («Prelude.isSome» («Prover.nrKey»
          (E.toList.map encEntry) r)).label ≠ 0 then acc else r :: acc) [] rs'' =
        rs''.filter fun r ↦ decide ¬(«Prelude.isSome» («Prover.nrKey»
          (E.toList.map encEntry) r)).label ≠ 0 :=
      fun rs'' ↦ rs''.rec rfl fun r rs'' ih ↦ by
        rw [List.foldr_cons, ih, List.filter_cons]
        split <;> simp_all
    rw [hd]
    refine List.filter_congr fun r hr ↦ ?_
    by_cases h1 : («Prover.nrKey» (E.toList.map encEntry) r).label = 1
    · obtain ⟨y, hy, hl⟩ := hK r hr h1
      have hne : («Prelude.get» («Prover.nrKey» (E.toList.map encEntry) r)).label ≠ x.label :=
        fun h ↦ hx ⟨y, hy, hl.trans h⟩
      simp [«Prover.keyFits», «Prelude.isSome», Const.eq, h1, hne]
    · simp [«Prover.keyFits», «Prelude.isSome», Const.eq, h1]

/-- The mirror's lifting of a renaming of leaves past a binder is the lifting of the renaming. -/
theorem liftR_eq (f : Tree → Tree) (f' : ℕ → ℕ) (hf : ∀ i, f (leaf i) = leaf (f' i)) (i : ℕ) :
    «Language.liftR» f (leaf i) = leaf (Internal.Term.liftR f' i) := by
  cases i <;> mirror_simp [«Language.liftR», Internal.Term.liftR, hf, beq_iff_eq,
    Nat.add_one_ne_zero, Nat.add_sub_cancel]

/-- The mirror's renaming of a node's child of an index below the node's number of children,
lifted past the variables the child binds, is the child's renaming of
{name}`Geb.FreeTopos.Internal.childRenamings`. -/
theorem childRen_eq (l : Internal.Label) (m j : ℕ) (hj : j < m) (f : Tree → Tree)
    (f' : ℕ → ℕ) (hf : ∀ i, f (leaf i) = leaf (f' i)) (a : ℕ) :
    «Prover.childRen» (leaf (labelData l).1) (leaf m) f (leaf j) (leaf a) =
      leaf ((Internal.childRenamings l m f').getD j f' a) := by
  have h1 := liftR_eq f f' hf
  have h2 : ∀ i, «Language.liftR» (fun x ↦ «Language.liftR» f x) (leaf i) =
      leaf (Internal.Term.liftR (Internal.Term.liftR f') i) := liftR_eq _ _ h1
  have hr : ∀ g : ℕ → ℕ, (List.replicate m g).getD j f' = g := fun g ↦ by
    simp [List.getD_eq_getElem?_getD, hj]
  cases l
  case lam =>
    rcases m with _ | _ | m
    · omega
    · obtain rfl : j = 0 := by omega
      mirror_simp [«Prover.childRen», labelData, Internal.childRenamings, h1]
    · mirror_simp [«Prover.childRen», labelData, Internal.childRenamings, hr, hf, beq_iff_eq,
      Nat.reduceEqDiff]
  case natRec =>
    rcases m with _ | _ | _ | _ | m
    any_goals mirror_simp [«Prover.childRen», labelData, Internal.childRenamings, hr, hf,
      beq_iff_eq, Nat.reduceEqDiff]
    rcases j with _ | _ | _ | j
    any_goals mirror_simp [«Prover.childRen», labelData, Internal.childRenamings, h1, hf,
      beq_iff_eq, Nat.reduceEqDiff]
    omega
  case listRec =>
    rcases m with _ | _ | _ | _ | m
    any_goals mirror_simp [«Prover.childRen», labelData, Internal.childRenamings, hr, hf,
      beq_iff_eq, Nat.reduceEqDiff]
    rcases j with _ | _ | _ | j
    any_goals mirror_simp [«Prover.childRen», labelData, Internal.childRenamings, h2, hf,
      beq_iff_eq, Nat.reduceEqDiff]
    omega
  case roseRec =>
    rcases m with _ | _ | _ | m
    any_goals mirror_simp [«Prover.childRen», labelData, Internal.childRenamings, hr, hf,
      beq_iff_eq, Nat.reduceEqDiff]
    rcases j with _ | _ | j
    any_goals mirror_simp [«Prover.childRen», labelData, Internal.childRenamings, h1, hf,
      beq_iff_eq, Nat.reduceEqDiff]
    omega
  all_goals mirror_simp [«Prover.childRen», labelData, Internal.childRenamings, hr, hf,
    beq_iff_eq, Nat.reduceEqDiff]

/-- Tests of a list, the first of the first term and so on, hold of a term and a list exactly when
the first holds of the term and the rest of the list. -/
theorem pairsHold_cons (p : Term → Bool) (ps : List (Term → Bool)) (u : Term) (us : List Term) :
    Internal.pairsHold (p :: ps) (u :: us) = (p u && Internal.pairsHold ps us) := by
  simp only [Internal.pairsHold, List.length_cons, List.zip_cons_cons, List.all_cons]
  cases p u <;> simp

/-- The mirror's fold testing a node's children against a pattern's, from a position, is the
test of the children's renamings, where the children's tests are related to the pattern's and the
renamings at the positions are those of {lit}`F`. -/
theorem holdAll_fold (l m : Tree) (f : Tree → Tree) (F : ℕ → ℕ → ℕ) :
    ∀ (xs : List (((Tree → Tree) → Tree → Tree) × ((ℕ → ℕ) → Term → Bool))),
    (∀ x ∈ xs, ∀ g g', (∀ i, g (leaf i) = leaf (g' i)) → ∀ u,
      x.1 g (encTerm u) = ofBool (x.2 g' u)) →
    ∀ (i : ℕ), (∀ j, i ≤ j → j < i + xs.length → ∀ a,
        «Prover.childRen» l m f (leaf j) (leaf a) = leaf (F j a)) →
      ∀ us : List Term,
        List.foldr (fun r (c : Tree → List Tree → Tree) i' vs ↦ Const.lcase vs (leaf 0)
            fun v ws ↦ «Prelude.and» (r («Prover.childRen» l m f i') v)
              (c (Const.add i' (leaf 1)) ws))
          (fun _ vs ↦ «Base.isEmpty» vs) (xs.map Prod.fst) (leaf i) (us.map encTerm) =
        ofBool (Internal.pairsHold ((xs.zipIdx i).map fun p ↦ p.1.2 (F p.2)) us) := by
  refine fun xs ↦ xs.rec (fun _ i _ us ↦ ?_) fun x xs ih hx i hF us ↦ ?_
  · cases us <;> rfl
  · rcases us with _ | ⟨u, us⟩
    · rfl
    · simp only [List.map_cons, List.foldr_cons, lcase_cons, List.zipIdx_cons, pairsHold_cons,
        add_leaf]
      rw [hx x List.mem_cons_self _ (F i) (hF i le_rfl (by simp) ) u,
        ih (fun y hy ↦ hx y (List.mem_cons_of_mem _ hy)) (i + 1)
          (fun j h1 h2 ↦ hF j (by omega) (by simp at h2 ⊢; omega)) us, and_eq]

/-- The renamings of a node's children are as many as the children. -/
theorem length_childRenamings (l : Internal.Label) (m : ℕ) (f : ℕ → ℕ) :
    (Internal.childRenamings l m f).length = m := by
  unfold Internal.childRenamings
  split <;> simp

/-- The test at a node other than a variable, at a term's node: the labels are equal and the
children's tests, each at its renaming, hold of the term's children. -/
theorem isRenameStep_node (l : Internal.Label) (hl : ∀ i, l ≠ .var i)
    (ws : List ((ℕ → ℕ) → Term → Bool)) (f : ℕ → ℕ) (lu : Internal.Label) (cs : List Term) :
    Internal.isRenameStep l ws f (RoseTree.node lu cs) =
      (decide (lu = l) &&
        Internal.pairsHold ((ws.zip (Internal.childRenamings l ws.length f)).map fun p ↦ p.1 p.2)
          cs) := by
  have hb : (lu == l) = decide (lu = l) := by
    by_cases h : lu = l
    · subst h
      simp
    · simp [h]
  cases l
  case var i => exact absurd rfl (hl i)
  all_goals simp only [Internal.isRenameStep, RoseTree.label_node, RoseTree.children_node, hb]

/-- The tests of the children at their renamings, by the positions of the tests. -/
theorem zip_renamings (ws : List ((ℕ → ℕ) → Term → Bool)) (rs : List (ℕ → ℕ)) (d : ℕ → ℕ)
    (h : rs.length = ws.length) :
    (ws.zipIdx 0).map (fun p ↦ p.1 (rs.getD p.2 d)) = (ws.zip rs).map fun p ↦ p.1 p.2 := by
  refine List.ext_getElem (by simp [h]) fun i h₁ h₂ ↦ ?_
  have hi : i < rs.length := by simp at h₁; omega
  simp [List.getElem_zipIdx, List.getD_eq_getElem?_getD, hi]

/-- The mirror's test at an encoded node other than a variable, at related tests of its
children. -/
theorem isRenameStep_eq_node (l : Internal.Label) (hl0 : (labelData l).1 ≠ 0)
    (hl : ∀ i, l ≠ .var i) (v : (Tree → Tree) → Tree → Tree)
    (xs : List (Term × ((Tree → Tree) → Tree → Tree) × ((ℕ → ℕ) → Term → Bool)))
    (hx : ∀ x ∈ xs, ∀ f f', (∀ i, f (leaf i) = leaf (f' i)) → ∀ u,
      x.2.1 f (encTerm u) = ofBool (x.2.2 f' u))
    (f : Tree → Tree) (f' : ℕ → ℕ) (hf : ∀ i, f (leaf i) = leaf (f' i)) (lu : Internal.Label)
    (cs : List Term) :
    «Prover.isRenameStep» (encTerm (RoseTree.node l (xs.map Prod.fst)))
        (v :: xs.map fun x ↦ x.2.1) f (encTerm (RoseTree.node lu cs)) =
      ofBool (Internal.isRenameStep l (xs.map fun x ↦ x.2.2) f' (RoseTree.node lu cs)) := by
  have hh := holdAll_fold (leaf (labelData l).1) (leaf xs.length) f
    (fun j ↦ (Internal.childRenamings l xs.length f').getD j f')
    (xs.map fun x ↦ (x.2.1, x.2.2))
    (fun y hy ↦ by
      obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hy
      exact hx x hx')
    0 (fun j _ hj a ↦ childRen_eq l xs.length j (by simpa using hj) f f' hf a) cs
  simp only [List.map_map, Function.comp_def] at hh
  rw [isRenameStep_node l hl, List.length_map, ← zip_renamings _ _ f'
    (by simp [length_childRenamings])]
  simp only [«Prover.isRenameStep», «Prover.holdAll», label_eq, label_encTerm,
    RoseTree.label_node, eq_leaf, equal_eq, child_encTerm, mArgs_eq, RoseTree.children_node,
    length_eq, List.length_map, label_ne_zero, ofBool_bne, beq_iff_eq, hl0, ↓reduceIte, foldr_eq]
  rw [show «Prover/RTs.tail» (v :: xs.map fun x ↦ x.2.1) = xs.map fun x ↦ x.2.1 from rfl, hh,
    and_eq, and_eq, ← Bool.and_assoc, labelData_beq lu l]
  simp only [List.zipIdx_map, List.map_map, Function.comp_def]
  rfl

/-- The mirror's test whether an encoded term is an encoded pattern renamed, at a renaming of
leaves. -/
theorem isRename_eq (p : Term) : ∀ (f : Tree → Tree) (f' : ℕ → ℕ),
    (∀ i, f (leaf i) = leaf (f' i)) → ∀ u : Term,
      «Prover.isRename» (encTerm p) f (encTerm u) = ofBool (Internal.isRename p f' u) := by
  simp only [«Prover.isRename», Internal.isRename, elim_eq_para]
  refine para_enc (fun l ↦ (labelData l).1) (fun l ↦ RoseTree.node 0 (labelData l).2)
    (fun (v : (Tree → Tree) → Tree → Tree) (w : (ℕ → ℕ) → Term → Bool) ↦
      ∀ f f', (∀ i, f (leaf i) = leaf (f' i)) → ∀ u, v f (encTerm u) = ofBool (w f' u))
    «Prover.isRenameStep» _ (fun l v xs hx f f' hf u ↦ ?_) p
  change «Prover.isRenameStep» (encTerm (RoseTree.node l (xs.map Prod.fst))) _ f (encTerm u) = _
  obtain ⟨lu, cs, rfl⟩ := exists_node u
  simp only [List.map_map, Function.comp_def]
  cases l
  case var i =>
    cases lu
    case var j =>
      have hb : (Internal.Label.var j == Internal.Label.var (f' i)) = (j == f' i) := by
        by_cases h : j = f' i
        · subst h
          simp
        · simp [h]
      mirror_simp [«Prover.isRenameStep», labelData, label_encTerm, mD_eq, mArgs_eq, hf,
        Internal.isRenameStep, hb]
    all_goals
      mirror_simp [«Prover.isRenameStep», labelData, label_encTerm, Internal.isRenameStep]
      rfl
  all_goals
    refine isRenameStep_eq_node _ ?_ ?_ v xs hx f f' hf lu cs
    · simp only [labelData]
      decide
    · intro _ h
      cases h

/-- An equation among the hypotheses as the mirror prepares it: present with its sides and the
test of its left side's renamings, or absent. -/
def encPH : Option (Term × Term) → Tree × Tree × Tree × ((Tree → Tree) → Tree → Tree)
  | some (l, r) => (leaf 1, encTerm l, encTerm r, «Prover.isRename» (encTerm l))
  | none => «Prover.ph0»

/-- The mirror's preparation of encoded hypotheses. -/
theorem prepareHyps_eq (Φ : List Term) :
    «Prover.prepareHyps» (Φ.map encTerm) = Φ.map fun ψ ↦ encPH (Internal.eqParts ψ) := by
  simp only [«Prover.prepareHyps», foldr_eq]
  exact Φ.rec rfl fun ψ Φ ih ↦ by
    simp only [List.map_cons, List.foldr_cons, ih, eqParts_eq]
    rcases Internal.eqParts ψ with _ | ⟨l, r⟩ <;> mirror_simp [encPH, p1_eq, p2_eq]

/-- The mirror's prepared hypothesis at a position, absent out of range. -/
theorem phAt_eq (xs : List (Tree × Tree × Tree × ((Tree → Tree) → Tree → Tree))) (i : ℕ) :
    «Prover.phAt» xs (leaf i) = xs.getD i «Prover.ph0» := by
  have hr : ∀ i : ℕ, Nat.repeat «Prover/PHs.tail» i xs = xs.drop i :=
    Nat.rec rfl fun i ih ↦ by
      rw [Nat.repeat, ih]
      cases h : xs.drop i
      · rw [List.drop_eq_nil_iff] at h
        rw [List.drop_eq_nil_of_le (by omega)]
        rfl
      · rw [← List.tail_drop, h]
        rfl
  simp only [«Prover.phAt», iter_leaf, hr, List.getD_eq_getElem?_getD]
  cases h : xs.drop i with
  | nil =>
    rw [List.drop_eq_nil_iff] at h
    rw [List.getElem?_eq_none h]
    rfl
  | cons x rest =>
    rw [← List.head?_drop, h]
    rfl

/-- The mirror's rewriting of an encoded term at its root by a rule related to a rule of the
normalizer, under the hypotheses weakened past a number of new innermost variables, the equations
among them prepared. -/
theorem tryRuleK_eq (r' : Tree × (Tree → Tree → List Tree → Tree)) (r : NormRule)
    (h : RRel r' r) (k : ℕ) (t : Term) :
    «Prover.tryRuleK» (encGlobals G) (E.toList.map encEntry) (leaf n) Γ (leaf k)
        (Φ.map encTerm) («Prover.prepareHyps» (Φ.map encTerm)) r' (encTerm t) =
      encOpt ((Internal.tryRuleK G E n Γ k Φ (Internal.prepareHyps Φ) t r).map encTD) := by
  cases r
  case rule l =>
    simp only [RRel] at h
    simp only [«Prover.tryRuleK», template, h, encRule]
    mirror_simp [List.getD_cons_zero, List.getD_cons_succ]
    rw [rootStepK_eq G E n Γ Φ k l t, mapO_eq, Option.map_map]
    simp only [Internal.tryRuleK, Option.map_map]
    rfl
  case hyp i =>
    simp only [RRel] at h
    simp only [«Prover.tryRuleK», template, h, encRule, prepareHyps_eq]
    mirror_simp [List.getD_cons_zero, phAt_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
      Internal.tryRuleK, Internal.prepareHyps]
    rcases Φ[i]? with _ | ψ
    · mirror_simp [«Prover.ph0», none_eq, bne_self_eq_false]
    rcases he : Internal.eqParts ψ with _ | ⟨l, r⟩
    · mirror_simp [encPH, he, «Prover.ph0», none_eq, bne_self_eq_false]
    by_cases hk : k = 0
    · subst hk
      by_cases htl : t = l
      · subst htl
        mirror_simp [encPH, he, weakenBy_eq, some_eq, beq_self_eq_true]
        rfl
      · mirror_simp [encPH, he, htl, encTerm_eq_iff, none_eq, beq_iff_eq, Nat.reduceBNe,
          decide_false, Bool.and_false]
    · have hr := isRename_eq l (fun x ↦ Const.add x (leaf k)) (· + k) (fun _ ↦ rfl) t
      by_cases ht : Internal.isRename l (· + k) t = true
      · simp only [Internal.isRename] at ht hr
        mirror_simp [encPH, he, hk, hr, ht, weakenBy_eq, some_eq, beq_iff_eq, Nat.reduceBNe,
          ofBool_true]
        rfl
      · simp only [Internal.isRename, Bool.not_eq_true] at ht hr
        mirror_simp [encPH, he, hk, hr, ht, none_eq, beq_iff_eq, Nat.reduceBNe, ofBool_false]
  case thmAt j θ root m k' =>
    obtain ⟨p, hp, h1, hm⟩ := h
    simp only [«Prover.tryRuleK», template, h1]
    mirror_simp [List.getD_cons_zero]
    exact tryRule_eq G E n Γ [] _ (.thmAt j θ root m k') ⟨p, hp, h1, hm⟩ t
  all_goals
    have h' := h
    simp only [RRel] at h'
    simp only [«Prover.tryRuleK», template, h', encRule]
    mirror_simp [List.getD_cons_zero]
    exact tryRule_eq G E n Γ [] _ _ h t

/-- Lists related elementwise are related after filters agreeing at related elements. -/
theorem forall₂_filter {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    List.Forall₂ R (l₁.filter p) (l₂.filter q) := by
  refine List.Forall₂.rec (motive := fun l₁ l₂ _ ↦ List.Forall₂ R (l₁.filter p) (l₂.filter q))
    .nil (fun {a b _ _} hab _ ih ↦ ?_) h
  rw [List.filter_cons, List.filter_cons, hpq a b hab]
  split
  · exact .cons hab ih
  · exact ih

/-- The mirror's rewriting at the root under weakened hypotheses by the index of rules related
to the normalizer's is the rewriting by the rules under the hypotheses weakened. -/
theorem rootRewriteK_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree)))
    (rs : List NormRule) (hrs : List.Forall₂ RRel rs' rs) (k : ℕ) (t : Term) :
    «Prover.rootRewriteK» (encGlobals G) (E.toList.map encEntry) (leaf n)
        («Prover.indexRules» (E.toList.map encEntry) rs') («Prover.prepareHyps» (Φ.map encTerm))
        Γ (leaf k) (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.rootRewrite G E n rs Γ (Φ.map (Internal.weakenBy k)) t).map encTD) := by
  have hf := forall₂_filter (p := fun r' ↦ decide ((«Prover.keyFits» (leaf t.label.rootKey)
      («Prover.nrKey» (E.toList.map encEntry) r')).label ≠ 0))
    (q := fun r ↦ Internal.keyFits t.label.rootKey (r.rootKey? E))
    (fun r' r h ↦ by rw [nrKey_eq E r' r h, keyFits_eq]; cases Internal.keyFits _ _ <;> rfl) hrs
  have hL : Internal.rootRewrite G E n rs Γ (Φ.map (Internal.weakenBy k)) t =
      (rs.filter fun r ↦ Internal.keyFits t.label.rootKey (r.rootKey? E)).findSome?
        (Internal.tryRuleK G E n Γ k Φ (Internal.prepareHyps Φ) t) := by
    rw [funext (Internal.tryRuleK_eq G E n Γ k Φ t), Internal.findSome?_filter _ _ _
      fun r _ h ↦ Internal.tryRule_eq_none G E n Γ _ t r h]
    rfl
  simp only [«Prover.rootRewriteK», template, foldr_eq, ruleBucket_eq, rootKey_eq, bucketOf_eq,
    hL]
  generalize rs'.filter _ = xs' at hf
  generalize rs.filter _ = xs at hf
  revert xs
  exact xs'.rec (fun xs h ↦ by cases h; rfl) fun r' xs' ih xs h ↦ by
    cases h with
    | cons hr h' =>
      simp only [List.foldr_cons, List.findSome?_cons, tryRuleK_eq G E n Γ Φ _ _ hr k t,
        isSome_eq, ih _ h']
      rcases Internal.tryRuleK G E n Γ k Φ (Internal.prepareHyps Φ) t _ with _ | x <;> rfl

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

/-- The mirror's rewriting at the root under weakened hypotheses and a rewriting at the root
under weakened hypotheses are related at the hypotheses {lit}`Φ` when they agree at every context,
number of variables and encoded term. -/
def WRel (Φ : List Term) (v : List Tree → Tree → List Tree → Tree → Tree)
    (w : Internal.RootRewriteK) : Prop :=
  ∀ Γ k t, v Γ (leaf k) (Φ.map encTerm) (encTerm t) = encOpt ((w Γ k Φ t).map encTD)

/-- The mirror's reduction under weakened hypotheses and a reduction under weakened hypotheses
are related at the hypotheses {lit}`Φ` when they agree at every depth, context, number of variables
and encoded term. -/
def EKRel (Φ : List Term) (v : Tree → List Tree → Tree → List Tree → Tree → Tree)
    (w : Internal.ReductionK) : Prop :=
  ∀ dp Γ k t, v (leaf (encDepth dp)) Γ (leaf k) (Φ.map encTerm) (encTerm t) =
    encOpt ((w dp Γ k Φ t).map encTDB)

/-- The mirror's rewriting at the root followed by a reduction, under weakened hypotheses, at
related rewritings and reductions. -/
theorem atRootK_eq (rw' : List Tree → Tree → List Tree → Tree → Tree) (rw : Internal.RootRewriteK)
    (hrw : WRel Φ rw' rw) (rec' : Tree → List Tree → Tree → List Tree → Tree → Tree)
    (rec : Internal.ReductionK) (hrec : EKRel Φ rec' rec) (k : ℕ) (dp : Internal.Depth)
    (t₁ : Term) (d₁ : Deriv × Bool) :
    «Prover.atRootK» rw' rec' Γ (leaf k) (Φ.map encTerm) (leaf (encDepth dp)) (encTerm t₁)
        (encDB d₁) =
      encOpt ((Internal.atRootK rw rec Γ k Φ dp t₁ d₁).map encTDB) := by
  simp only [«Prover.atRootK», template, Internal.atRootK, hrw Γ k t₁, isSome_eq]
  rcases rw Γ k Φ t₁ with _ | ⟨t₂, dr⟩
  · rfl
  · have h2 : «Language.pr» (encDeriv dr) (leaf 1) = encDB (dr, true) := rfl
    simp only [Option.map_some, Option.isSome_some, ofBool_true, label_leaf, ne_eq,
      one_ne_zero, not_false_eq_true, ↓reduceIte, tmpl_fromMaybe_eq, Option.getD_some,
      p1_encTD,
      p2_encTD, hrec dp Γ k t₂, mapO_eq, Option.map_map, h2]
    rcases rec dp Γ k Φ t₂ with _ | ⟨t₃, d₃⟩
    · rfl
    · simp only [Option.map_some, Function.comp_apply, p1_encTDB, p2_encTDB, dTrans_eq]
      rfl

/-- A label's position is the application's exactly at the application. -/
theorem labelData_eq_app (l : Internal.Label) : (labelData l).1 = 6 ↔ l = .app := by
  cases l <;> simp [labelData]

/-- A label's position is the abstraction's exactly at an abstraction. -/
theorem labelData_eq_lam (l : Internal.Label) : (labelData l).1 = 5 ↔ ∃ a, l = .lam a := by
  cases l <;> simp [labelData]

/-- The mirror's step of the weak head normal form under weakened hypotheses, at related
rewritings at the root and reductions of the subterms. -/
theorem headStepK_eq (rw' : List Tree → Tree → List Tree → Tree → Tree)
    (rw : Internal.RootRewriteK) (hrw : WRel Φ rw' rw)
    (rec' : Tree → List Tree → Tree → List Tree → Tree → Tree) (rec : Internal.ReductionK)
    (hrec : EKRel Φ rec' rec) (k : ℕ) (t : Term) :
    «Prover.headStepK» rw' rec' Γ (leaf k) (Φ.map encTerm) (encTerm t) =
      encOpt ((Internal.headStepK rw rec Γ k Φ t).map encTDB) := by
  have h0 : ∀ Γ t, rec' (leaf 0) Γ (leaf k) (Φ.map encTerm) (encTerm t) =
      encOpt ((rec .head Γ k Φ t).map encTDB) := fun Γ t ↦ hrec .head Γ k t
  have h1 : ∀ Γ t, rec' (leaf 1) Γ (leaf k) (Φ.map encTerm) (encTerm t) =
      encOpt ((rec .weak Γ k Φ t).map encTDB) := fun Γ t ↦ hrec .weak Γ k t
  have hA : ∀ t₁ d₁, «Prover.atRootK» rw' rec' Γ (leaf k) (Φ.map encTerm) (leaf 0) (encTerm t₁)
      (encDB d₁) = encOpt ((Internal.atRootK rw rec Γ k Φ .head t₁ d₁).map encTDB) :=
    atRootK_eq Γ Φ rw' rw hrw rec' rec hrec k .head
  obtain ⟨l, ts, rfl⟩ : ∃ l ts, t = RoseTree.node l ts :=
    ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩
  by_cases happ : (labelData l).1 = 6 ∧ ts.length = 2
  · obtain ⟨hl, h2⟩ := happ
    obtain rfl := (labelData_eq_app l).mp hl
    match ts, h2 with
    | [f, u], _ =>
      simp only [«Prover.headStepK», template, Internal.headStepK]
      mirror_simp [mIs_eq, labelData, mArg_eq, h0]
      rcases rec .head Γ k Φ f with _ | ⟨f', df⟩
      · rfl
      have hL : ∀ (u' : Term) (du : Deriv × Bool), «Prover.atRootK» rw' rec' Γ (leaf k)
          (Φ.map encTerm) (leaf 0) («Language.app» (encTerm f') (encTerm u'))
          («Prover.dCong» («Theory.l2» (encDB df) (encDB du))) =
          encOpt ((Internal.atRootK rw rec Γ k Φ .head (Term.app f' u')
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
            rcases rec .weak Γ k Φ u with _ | ⟨u', du⟩
            · rfl
            · simp only [Option.map_some, Option.elim_some, p1_encTDB, p2_encTDB, hL,
                Option.bind_some]
      · mirror_simp [mIs_eq, Bool.and_eq_true, beq_iff_eq, hlam, Option.bind_eq_bind]
        split
        · exact absurd ⟨(labelData_eq_lam _).mpr ⟨_, rfl⟩, rfl⟩ hlam
        · rcases rec .head Γ k Φ u with _ | ⟨u', du⟩
          · rfl
          · simp only [Option.map_some, Option.elim_some, p1_encTDB, p2_encTDB, hL,
              Option.bind_some]
  · generalize hM : «Prover.headStepK» rw' rec' Γ (leaf k) (Φ.map encTerm)
      (encTerm (RoseTree.node l ts)) = M
    simp only [Internal.headStepK, RoseTree.label_node, RoseTree.children_node]
    split
    · exact absurd ⟨rfl, rfl⟩ happ
    subst hM
    simp only [«Prover.headStepK», template]
    mirror_simp [mIs_eq, Bool.and_eq_true, beq_iff_eq, happ, hrw Γ k]
    rcases rw Γ k Φ (RoseTree.node l ts) with _ | ⟨t₁, dr⟩
    · mirror_simp [headChild_eq]
      rcases Internal.headChild l ts with _ | i
      · rfl
      mirror_simp [mArgs_eq, Option.bind_eq_bind]
      rcases ts[i]? with _ | c
      · rfl
      mirror_simp [h0]
      rcases rec .head Γ k Φ c with _ | ⟨c', dd, _ | _⟩
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
      rcases rec .head Γ k Φ t₁ with _ | ⟨t₂, d₂⟩
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

/-- The smaller of two numbers, as the mirror chooses it. -/
theorem ite_lt_leaf (a b : ℕ) :
    (if decide (a < b) = true then leaf a else leaf b) = leaf (min a b) := by
  by_cases h : a < b
  · simp [h, Nat.min_eq_left h.le]
  · simp [h, Nat.min_eq_right (Nat.le_of_not_lt h)]

/-- The mirror's reduction past a weak head normal form under weakened hypotheses, to a depth
past it, at related rewritings at the root and reductions of the subterms. -/
theorem deepStepK_eq (rw' : List Tree → Tree → List Tree → Tree → Tree)
    (rw : Internal.RootRewriteK) (hrw : WRel Φ rw' rw)
    (rec' : Tree → List Tree → Tree → List Tree → Tree → Tree) (rec : Internal.ReductionK)
    (hrec : EKRel Φ rec' rec) (dp : Internal.Depth) (hdp : dp ≠ .head) (k : ℕ) (w : Term)
    (dw : Deriv × Bool) :
    «Prover.deepStepK» (encGlobals G) (leaf n) rw' rec' (leaf (encDepth dp)) Γ (leaf k)
        (Φ.map encTerm) (encTerm w) (encDB dw) =
      encOpt ((Internal.deepStepK G n rw rec dp Γ k Φ w dw).map encTDB) := by
  have hC : ∀ cs : List (Term × Deriv × Bool), «Prover.dCong»
      (cs.map fun x ↦ encDB x.2) = encDB (Internal.dCong (cs.map Prod.snd)) := fun cs ↦ by
    rw [← dCong_eq, List.map_map]
    rfl
  obtain ⟨l, ts, rfl⟩ : ∃ l ts, w = RoseTree.node l ts :=
    ⟨w.label, w.children, (RoseTree.node_label_children w).symm⟩
  cases dp with
  | head => exact absurd rfl hdp
  | weak =>
    simp only [«Prover.deepStepK», template, Internal.deepStepK, encDepth]
    mirror_simp [label_encTerm, mArgs_eq, Option.bind_eq_bind]
    rw [allSomeT_range_zipIdx ts _ (fun x ↦ (if Internal.keepsWeak l x.2 = true then
      some (x.1, Internal.dRefl) else rec .weak Γ k Φ x.1).map encTDB) fun i hi ↦ by
        rw [keepsWeak_eq, getD_map_of_lt _ _ i hi]
        cases Internal.keepsWeak l i
        · exact hrec .weak Γ k ts[i]
        · rfl, Infer.mapM_map_option]
    refine bindO_list _ encTDB _ _ fun cs ↦ ?_
    have hA := atRootK_eq Γ Φ rw' rw hrw rec' rec hrec k .weak
    mirror_simp [RoseTree.children_node, marked_eq, rebuild_eq, p2_encTDB, hC, dTrans_eq]
    cases cs.any fun x ↦ x.2.2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [↓reduceIte]
      exact hA _ _
  | «open» =>
    simp only [«Prover.deepStepK», template, Internal.deepStepK, encDepth]
    mirror_simp [label_encTerm, mArgs_eq, childBinders_eq, Option.bind_eq_bind]
    rcases Internal.childBinders G n l ts Γ with _ | Bs
    · rfl
    mirror_simp [ite_lt_leaf, ← List.length_zip, range_eq, List.map_map, Function.comp_def]
    rw [allSomeT_range_zipIdx (Bs.zip ts) _ (fun x ↦ (if Internal.keepsFold l x.2 = true then
      some (x.1.2, Internal.dRefl) else rec .open x.1.1.1 (k + x.1.1.2) Φ x.1.2).map encTDB)
      fun i hi ↦ by
        have h1 : i < Bs.length := by simp at hi; omega
        have h2 : i < ts.length := by simp at hi; omega
        rw [keepsFold_eq]
        simp only [getD_map_of_lt _ _ i h1, getD_map_of_lt _ _ i h2, List.getElem_zip,
          encBinder, binderCtx_pair, binderNum_pair, add_leaf]
        cases Internal.keepsFold l i
        · mirror_simp []
          exact hrec .open _ _ _
        · rfl, Infer.mapM_map_option]
    refine bindO_list _ encTDB _ _ fun cs ↦ ?_
    have hA := atRootK_eq Γ Φ rw' rw hrw rec' rec hrec k .open
    mirror_simp [RoseTree.children_node, marked_eq, rebuild_eq, p2_encTDB, hC, dTrans_eq]
    cases cs.any fun x ↦ x.2.2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [↓reduceIte]
      exact hA _ _
  | full =>
    have h2 : ∀ dr : Deriv, «Language.pr» (encDeriv dr) (leaf 1) = encDB (dr, true) :=
      fun _ ↦ rfl
    have h3 : ∀ t, rec' (leaf 3) Γ (leaf k) (Φ.map encTerm) (encTerm t) =
        encOpt ((rec .full Γ k Φ t).map encTDB) := hrec .full Γ k
    simp only [«Prover.deepStepK», template, Internal.deepStepK, encDepth]
    mirror_simp [label_encTerm, mArgs_eq, childBinders_eq, Option.bind_eq_bind]
    rcases Internal.childBinders G n l ts Γ with _ | Bs
    · rfl
    mirror_simp [ite_lt_leaf, ← List.length_zip, range_eq, List.map_map, Function.comp_def]
    rw [allSomeT_range (Bs.zip ts) _ (fun x ↦ (rec .full x.1.1 (k + x.1.2) Φ x.2).map encTDB)
      fun i hi ↦ by
        have h1 : i < Bs.length := by simp at hi; omega
        have h2 : i < ts.length := by simp at hi; omega
        simp only [getD_map_of_lt _ _ i h1, getD_map_of_lt _ _ i h2, List.getElem_zip,
          encBinder, binderCtx_pair, binderNum_pair, add_leaf]
        exact hrec .full _ _ _, Infer.mapM_map_option]
    refine bindO_list _ encTDB _ _ fun cs ↦ ?_
    mirror_simp [RoseTree.children_node, rebuild_eq, p2_encTDB, hC, hrw Γ k]
    rcases rw Γ k Φ (RoseTree.node l (cs.map Prod.fst)) with _ | ⟨t₂, dr⟩
    · simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, dTrans_eq]
      rfl
    · mirror_simp [p1_encTD, p2_encTD, h2, h3]
      rcases rec .full Γ k Φ t₂ with _ | ⟨t₃, d₃⟩
      · rfl
      · simp only [Option.map_some, p1_encTDB, p2_encTDB, dTrans_eq]
        rfl

/-- The mirror's step of the reduction to a depth under weakened hypotheses, at related
rewritings at the root and reductions of the subterms. -/
theorem evalStepK_eq (rw' : List Tree → Tree → List Tree → Tree → Tree)
    (rw : Internal.RootRewriteK) (hrw : WRel Φ rw' rw)
    (rec' : Tree → List Tree → Tree → List Tree → Tree → Tree) (rec : Internal.ReductionK)
    (hrec : EKRel Φ rec' rec) :
    EKRel Φ («Prover.evalStepK» (encGlobals G) (leaf n) rw' rec')
      (Internal.evalStepK G n rw rec) := by
  intro dp Γ k t
  simp only [«Prover.evalStepK», template, Internal.evalStepK,
    headStepK_eq Γ Φ rw' rw hrw rec' rec hrec k, bindO_eq, Option.bind_eq_bind]
  rcases Internal.headStepK rw rec Γ k Φ t with _ | ⟨w, dw⟩
  · rfl
  cases dp with
  | head => rfl
  | weak => exact deepStepK_eq G n Γ Φ rw' rw hrw rec' rec hrec .weak nofun k w dw
  | «open» => exact deepStepK_eq G n Γ Φ rw' rw hrw rec' rec hrec .open nofun k w dw
  | full => exact deepStepK_eq G n Γ Φ rw' rw hrw rec' rec hrec .full nofun k w dw

/-- The mirror's reduction to a depth under weakened hypotheses within a depth of fuel, at a
related rewriting at the root. -/
theorem evalK_eq (rw' : List Tree → Tree → List Tree → Tree → Tree) (rw : Internal.RootRewriteK)
    (hrw : WRel Φ rw' rw) (fuel : ℕ) :
    EKRel Φ («Prover.evalK» (encGlobals G) (leaf n) rw' (leaf fuel))
      (Internal.evalK G n rw fuel) := by
  simp only [«Prover.evalK», template, iter_leaf, Internal.evalK]
  exact Nat.rec (fun _ _ _ _ ↦ rfl)
    (fun _ ih ↦ by rw [Nat.repeat]; exact evalStepK_eq G n Φ rw' rw hrw _ _ ih) fuel

/-- The mirror's reduction to a depth within a depth of fuel, at related rules: the reduction
under weakened hypotheses by the index of the rules and the prepared hypotheses, which
{name}`Geb.FreeTopos.Internal.evalK_eq` relates to the reduction. -/
theorem eval_eq (rs' : List (Tree × (Tree → Tree → List Tree → Tree))) (rs : List NormRule)
    (hrs : List.Forall₂ RRel rs' rs) (fuel : ℕ) :
    ERel («Prover.eval» (encGlobals G) (E.toList.map encEntry) (leaf n) rs'
        (leaf fuel))
      (Internal.eval G E n rs fuel) := by
  intro dp Γ Φ t
  have hw : WRel Φ («Prover.rootRewriteK» (encGlobals G) (E.toList.map encEntry) (leaf n)
      («Prover.indexRules» (E.toList.map encEntry) rs') («Prover.prepareHyps» (Φ.map encTerm)))
      (fun Γ k _ t ↦ Internal.rootRewrite G E n rs Γ (Φ.map (Internal.weakenBy k)) t) :=
    fun Γ k t ↦ rootRewriteK_eq G E n Γ Φ rs' rs hrs k t
  have h := evalK_eq G n Φ _ _ hw fuel dp Γ 0 t
  rw [Internal.evalK_eq G E n rs Φ _ (fun _ _ _ ↦ rfl) fuel dp Γ 0 t,
    Internal.map_weakenBy_zero] at h
  simpa only [«Prover.eval»] using h

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

end GebTests.Prototypes.FreeTopos.Agreement.Prove

end
