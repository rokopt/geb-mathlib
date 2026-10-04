/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Base

set_option doc.verso true in
/-!
# Partial Horn logic in the checker written in Geb

The functions of {lit}`bootstrap/free-topos/partial-horn.geb`, in the Lean the bootstrap compiler
emits ({lit}`GebMirror.Metalogic`), agree with the partial Horn logic's Lean definitions at every
encoded input: the sorts, scope and substitution of terms, the operations on equations and
sequents, the checker of certificates, and the extension of a theory by definitions.

## Main definitions

* {lit}`ChkRel` — the relation of the mirror's checker of a certificate to the checker's.

## Main statements

* {lit}`sortOf_eq`, {lit}`scoped_eq`, {lit}`phSubst_eq` — the sorts, scope and substitution of
  terms.
* {lit}`pcheck_eq` — the checker of certificates.
* {lit}`thyExtendAll_eq` — the extension of a theory by definitions.

## Tags

partial Horn logic, proof checker, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.PartialHorn

open Geb Geb.Kernel GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Fold GebTests.Prototypes.FreeTopos.Agreement.Base
open scoped FinEnum

/-- The trees of a list of trees with their results. -/
@[simp] theorem ptTrees_eq (rs : List (Tree × Tree)) :
    «PartialHorn.ptTrees» rs = rs.map Prod.fst :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«PartialHorn.ptTrees», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The results of a list of trees with their results. -/
@[simp] theorem ptValues_eq (rs : List (Tree × Tree)) :
    «PartialHorn.ptValues» rs = rs.map Prod.snd :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«PartialHorn.ptValues», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The argument sorts of an encoded signature. -/
@[simp] theorem opArgs_eq (o : List ℕ × ℕ) :
    «PartialHorn.opArgs» (encOpSig o) = o.1.map leaf := by
  simp [«PartialHorn.opArgs», encOpSig]

/-- The sort of an encoded signature. -/
@[simp] theorem opSort_eq (o : List ℕ × ℕ) :
    «PartialHorn.opSort» (encOpSig o) = leaf o.2 := by
  simp [«PartialHorn.opSort», encOpSig]

/-- The encoding of an optional number is injective. -/
theorem encOptLeaf_inj {a b : Option ℕ} : encOpt (a.map leaf) = encOpt (b.map leaf) ↔ a = b := by
  rw [encOpt_inj]
  exact Option.map_injective (fun _ _ ↦ leaf_inj.mp) |>.eq_iff

/-- The mirror's sort of a term in a context of sorts is the encoding of its sort. -/
theorem sortOf_eq (S : PartialHorn.Sig) (Γ : List ℕ) (t : Tree) :
    «PartialHorn.sortOf» (S.map encOpSig) (Γ.map leaf) t =
      encOpt ((PartialHorn.sortOf S Γ t).map leaf) := by
  simp only [«PartialHorn.sortOf», PartialHorn.sortOf]
  apply fold_pair_snd (fun (v : Tree) (w : Option ℕ) ↦ v = encOpt (w.map leaf))
  · intro l rs
    simp
  intro l xs hx
  cases l with
  | zero =>
    rcases xs with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp [none_eq, List.getElem?_map]
    split <;> rfl
  | succ k =>
    simp only [eq_leaf, ofBool_label, sub_leaf, nth_eq, bindO_eq, List.getElem?_map, beq_iff_eq,
      Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    cases S[k]? with
    | none => rfl
    | some o =>
      have hv : xs.map (fun x ↦ x.2.1) = (xs.map fun x ↦ x.2.2).map fun w ↦ encOpt (w.map leaf) :=
        by rw [List.map_map]; exact List.map_congr_left hx
      have inj : Function.Injective fun (w : Option ℕ) ↦ encOpt (w.map leaf) :=
        fun _ _ h ↦ encOptLeaf_inj.mp h
      simp only [Option.map_some, Option.elim_some, Option.bind_some, ptValues_eq, opArgs_eq,
        mapT_eq, List.map_map, Function.comp_def, equalTs_eq, ofBool_label, decide_eq_true_eq]
      have hs : o.1.map (fun a ↦ «Prelude.some» (leaf a)) =
          (o.1.map some).map fun w ↦ encOpt (w.map leaf) := by
        rw [List.map_map]
        rfl
      rw [hv, hs]
      simp only [(List.map_injective_iff.mpr inj).eq_iff]
      split <;> rfl

/-- The mirror's test of a term's variables' scope is the encoding of the test. -/
theorem scoped_eq (n : ℕ) (t : Tree) :
    «PartialHorn.scoped» (leaf n) t = ofBool (PartialHorn.Scoped n t) := by
  simp only [«PartialHorn.scoped», PartialHorn.Scoped]
  apply fold_pair_snd (fun (v : Tree) (w : Bool) ↦ v = ofBool w)
  · intro l rs
    simp
  intro l xs hx
  cases l with
  | zero =>
    rcases xs with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp <;> rfl
  | succ k =>
    simp only [eq_leaf, ofBool_label, beq_iff_eq, Nat.add_one_ne_zero, ↓reduceIte, ptValues_eq,
      List.map_map, Function.comp_def, List.all_map]
    rw [List.map_congr_left hx, allT_ofBool]

/-- The mirror's application of an operation. -/
@[simp] theorem phOp_eq (k : ℕ) (ts : List Tree) :
    «PartialHorn.phOp» (leaf k) ts = PartialHorn.op k ts := rfl

/-- The mirror's variable of an index. -/
@[simp] theorem phVar_eq (i : ℕ) : «PartialHorn.phVar» (leaf i) = PartialHorn.var i := rfl

/-- The mirror's substitution of terms for a term's variables is the substitution. -/
theorem phSubst_eq (ts : List Tree) (t : Tree) :
    «PartialHorn.phSubst» ts t = PartialHorn.subst ts t := by
  simp only [«PartialHorn.phSubst», PartialHorn.subst]
  apply fold_pair_snd (fun (v w : Tree) ↦ v = w)
  · intro l rs
    simp
  intro l xs hx
  have hv : «PartialHorn.ptValues» (xs.map fun x ↦ (x.1, x.2.1)) =
      (xs.map fun x ↦ (x.1, x.2.2)).map Prod.snd := by
    simp only [ptValues_eq, List.map_map, Function.comp_def]
    exact List.map_congr_left hx
  rw [hv]
  cases l with
  | zero =>
    rcases xs with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp
  | succ k => simp

/-- The mirror's equation of two sides. -/
@[simp] theorem eqn_eq (a b : Tree) : «PartialHorn.eqn» a b = encEqn ⟨a, b⟩ := rfl

/-- The mirror's left side of an equation. -/
@[simp] theorem eqLhs_eq (q : PartialHorn.Eqn) : «PartialHorn.eqLhs» (encEqn q) = q.lhs := by
  simp [«PartialHorn.eqLhs», encEqn]

/-- The mirror's right side of an equation. -/
@[simp] theorem eqRhs_eq (q : PartialHorn.Eqn) : «PartialHorn.eqRhs» (encEqn q) = q.rhs := by
  simp [«PartialHorn.eqRhs», encEqn]

/-- The mirror's substitution in an equation. -/
@[simp] theorem eqSubst_eq (ts : List Tree) (q : PartialHorn.Eqn) :
    «PartialHorn.eqSubst» ts (encEqn q) = encEqn (q.subst ts) := by
  simp [«PartialHorn.eqSubst», phSubst_eq, PartialHorn.Eqn.subst]

/-- The mirror's test of an equation's scope. -/
@[simp] theorem eqScoped_eq (n : ℕ) (q : PartialHorn.Eqn) :
    «PartialHorn.eqScoped» (leaf n) (encEqn q) = ofBool (q.Scoped n) := by
  simp [«PartialHorn.eqScoped», scoped_eq, PartialHorn.Eqn.Scoped]

/-- The mirror's context of a sequent. -/
@[simp] theorem seqCtx_eq (a : PartialHorn.Seq) :
    «PartialHorn.seqCtx» (encSeq a) = a.ctx.map leaf := by
  simp [«PartialHorn.seqCtx», encSeq]

/-- The mirror's hypotheses of a sequent. -/
@[simp] theorem seqHyps_eq (a : PartialHorn.Seq) :
    «PartialHorn.seqHyps» (encSeq a) = a.hyps.map encEqn := by
  simp [«PartialHorn.seqHyps», encSeq]

/-- The mirror's conclusion of a sequent. -/
@[simp] theorem seqConcl_eq (a : PartialHorn.Seq) :
    «PartialHorn.seqConcl» (encSeq a) = encEqn a.concl := by
  simp [«PartialHorn.seqConcl», encSeq]

/-- The mirror's sequent of a context, hypotheses and a conclusion. -/
@[simp] theorem mkSeq_eq (ctx : List ℕ) (hs : List PartialHorn.Eqn) (q : PartialHorn.Eqn) :
    «PartialHorn.mkSeq» (ctx.map leaf) (hs.map encEqn) (encEqn q) = encSeq ⟨ctx, hs, q⟩ :=
  rfl

/-- The mirror's test of a sequent's scope. -/
@[simp] theorem seqScoped_eq (a : PartialHorn.Seq) :
    «PartialHorn.seqScoped» (encSeq a) = ofBool a.Scoped := by
  simp only [«PartialHorn.seqScoped», seqCtx_eq, seqHyps_eq, seqConcl_eq, length_eq,
    List.length_map, PartialHorn.Seq.Scoped]
  rw [allT_map _ encEqn (fun h ↦ h.Scoped a.ctx.length) _ fun q _ ↦ eqScoped_eq _ q,
    eqScoped_eq, and_eq]

/-- The mirror's signature of a theory. -/
@[simp] theorem thySig_eq (T : PartialHorn.Theory) :
    «PartialHorn.thySig» (encTheory T) = T.sig.map encOpSig := by
  simp [«PartialHorn.thySig», encTheory]

/-- The mirror's axioms of a theory. -/
@[simp] theorem thyAxioms_eq (T : PartialHorn.Theory) :
    «PartialHorn.thyAxioms» (encTheory T) = T.axioms.map encSeq := by
  simp [«PartialHorn.thyAxioms», encTheory]

/-- A result of the checker written in Geb represents a result of the Lean checker when, at
every encoded context and hypotheses, it is the encoding of the Lean checker's. -/
def ChkRel (v : List Tree → List Tree → Tree) (w : PartialHorn.Chk) : Prop :=
  ∀ Γ H, v (Γ.map leaf) (H.map encEqn) = encOpt ((w Γ H).map encEqn)

/-- The certificates of a list of certificates with their results. -/
@[simp] theorem pcTrees_eq (rs : List (Tree × (List Tree → List Tree → Tree))) :
    «PartialHorn.pcTrees» rs = rs.map Prod.fst :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«PartialHorn.pcTrees», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The results of a list of certificates with their results, at a context and hypotheses. -/
@[simp] theorem pcResults_eq (rs : List (Tree × (List Tree → List Tree → Tree)))
    (ctx hs : List Tree) :
    «PartialHorn.pcResults» rs ctx hs = rs.map fun r ↦ r.2 ctx hs :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«PartialHorn.pcResults», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- A list of certificates with their results without its head. -/
@[simp] theorem pcTail_eq (rs : List (Tree × (List Tree → List Tree → Tree))) :
    «PartialHorn.pcTail» rs = rs.tail := by
  cases rs <;> rfl

/-- Dropping the head of a list of certificates as many times as a label. -/
theorem repeat_pcTail (rs : List (Tree × (List Tree → List Tree → Tree))) :
    ∀ i : ℕ, Nat.repeat «PartialHorn.pcTail» i rs = rs.drop i :=
  Nat.rec rfl fun i ih ↦ by rw [Nat.repeat, ih, pcTail_eq, List.tail_drop]

/-- The result of a premise at a position, the absent result out of range. -/
@[simp] theorem pcPrem_eq (rs : List (Tree × (List Tree → List Tree → Tree))) (i : ℕ) :
    «PartialHorn.pcPrem» rs (leaf i) =
      (rs[i]?.map Prod.snd).getD fun _ _ ↦ encOpt none := by
  simp only [«PartialHorn.pcPrem», iter_leaf, repeat_pcTail]
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

/-- The mirror's index a leaf names. -/
@[simp] theorem leafIndex_eq (t : Tree) :
    «PartialHorn.leafIndex» t = encOpt ((PartialHorn.leafIndex t).map leaf) := by
  simp only [«PartialHorn.leafIndex», PartialHorn.leafIndex, arity_eq, eq_leaf,
    ofBool_label, length_beq_zero, label_eq]
  split <;> rfl

/-- The encoding of equations is injective. -/
@[simp] theorem encEqn_inj {q q' : PartialHorn.Eqn} : encEqn q = encEqn q' ↔ q = q' := by
  refine ⟨fun h ↦ ?_, congrArg encEqn⟩
  have := congrArg RoseTree.children h
  simp only [encEqn, RoseTree.children_node, List.cons.injEq, and_true] at this
  exact PartialHorn.Eqn.ext this.1 this.2

/-- The encoding of lists of equations is injective. -/
@[simp] theorem map_encEqn_inj {hs hs' : List PartialHorn.Eqn} :
    hs.map encEqn = hs'.map encEqn ↔ hs = hs' :=
  List.map_inj_right fun _ _ ↦ encEqn_inj.mp

/-- The encoding of optional equations is injective. -/
theorem encOptEqn_inj :
    Function.Injective fun (o : Option PartialHorn.Eqn) ↦ encOpt (o.map encEqn) := by
  intro a b h
  refine Option.map_injective (fun q q' e ↦ ?_) (encOpt_inj.mp h)
  have := congrArg RoseTree.children e
  simp only [encEqn, RoseTree.children_node, List.cons.injEq, and_true] at this
  exact PartialHorn.Eqn.ext this.1 this.2

/-- The mirror's sort of a term, as a function. -/
theorem sortOf_fun (S : PartialHorn.Sig) (Γ : List ℕ) :
    «PartialHorn.sortOf» (S.map encOpSig) (Γ.map leaf) =
      fun t ↦ encOpt ((PartialHorn.sortOf S Γ t).map leaf) :=
  funext (sortOf_eq S Γ)

/-- The encoding of optional trees is injective. -/
theorem encOpt_injective : Function.Injective encOpt := fun _ _ h ↦ encOpt_inj.mp h

/-- The mirror's instance of a sequent at the terms and premises of a certificate's node. -/
theorem inst_eq (S : PartialHorn.Sig) (a : PartialHorn.Seq)
    (xs : List (Tree × (List Tree → List Tree → Tree) × PartialHorn.Chk))
    (hx : ∀ x ∈ xs, ChkRel x.2.1 x.2.2) (Γ : List ℕ) (H : List PartialHorn.Eqn) :
    «PartialHorn.inst» (S.map encOpSig) (encSeq a) (xs.map fun x ↦ (x.1, x.2.1))
        (Γ.map leaf) (H.map encEqn) =
      encOpt ((PartialHorn.inst S a (xs.map fun x ↦ (x.1, x.2.2)) Γ H).map encEqn) := by
  set cs := xs.map fun x ↦ (x.1, x.2.2) with hcs
  have hres : (xs.map fun x ↦ (x.1, x.2.1)).map (fun r ↦ r.2 (Γ.map leaf) (H.map encEqn)) =
      cs.map fun c ↦ encOpt ((c.2 Γ H).map encEqn) := by
    simp only [hcs, List.map_map, Function.comp_def]
    exact List.map_congr_left fun x h ↦ hx x h Γ H
  have hts : List.take a.ctx.length (List.map Prod.fst (xs.map fun x ↦ (x.1, x.2.1))) =
      List.map Prod.fst (List.take a.ctx.length cs) := by
    simp [hcs, List.map_take, List.map_map, Function.comp_def]
  have c2 : decide (List.map («PartialHorn.sortOf» (S.map encOpSig) (Γ.map leaf))
        (List.map Prod.fst (List.take a.ctx.length cs)) =
        List.map «Prelude.some» (List.map leaf a.ctx)) =
      decide (List.map (PartialHorn.sortOf S Γ) (List.map Prod.fst (List.take a.ctx.length cs)) =
        List.map some a.ctx) := by
    have inj : Function.Injective fun (w : Option ℕ) ↦ encOpt (w.map leaf) :=
      fun _ _ h ↦ encOptLeaf_inj.mp h
    rw [sortOf_fun, decide_eq_decide, ← (List.map_injective_iff.mpr inj).eq_iff]
    simp only [List.map_map, Function.comp_def, Option.map_some]
    rfl
  have c3 : decide (List.map («Base.mapO» «PartialHorn.eqLhs»)
        (List.take a.ctx.length (List.drop a.ctx.length
          (cs.map fun c ↦ encOpt ((c.2 Γ H).map encEqn)))) =
        List.map «Prelude.some» (List.map Prod.fst (List.take a.ctx.length cs))) =
      decide (List.map (fun (c : Tree × PartialHorn.Chk) ↦ (c.2 Γ H).map PartialHorn.Eqn.lhs)
        (List.take a.ctx.length (List.drop a.ctx.length cs)) =
        List.map some (List.map Prod.fst (List.take a.ctx.length cs))) := by
    rw [decide_eq_decide, ← (List.map_injective_iff.mpr encOpt_injective).eq_iff]
    simp only [List.map_map, Function.comp_def, ← List.map_drop, ← List.map_take, mapO_eq,
      Option.map_map, eqLhs_eq, some_eq]
  have c4 : decide (List.drop (a.ctx.length + a.ctx.length)
        (cs.map fun c ↦ encOpt ((c.2 Γ H).map encEqn)) =
        List.map (fun x8 ↦ «Prelude.some» («PartialHorn.eqSubst»
          (List.map Prod.fst (List.take a.ctx.length cs)) x8)) (List.map encEqn a.hyps)) =
      decide (List.map (fun (c : Tree × PartialHorn.Chk) ↦ c.2 Γ H)
        (List.drop (a.ctx.length + a.ctx.length) cs) =
        List.map (fun h ↦ some (h.subst (List.map Prod.fst (List.take a.ctx.length cs))))
          a.hyps) := by
    rw [decide_eq_decide, ← (List.map_injective_iff.mpr encOptEqn_inj).eq_iff]
    simp only [List.map_map, Function.comp_def, ← List.map_drop, eqSubst_eq, some_eq,
      Option.map_some]
  simp only [«PartialHorn.inst», seqCtx_eq, length_eq, List.length_map, pcTrees_eq,
    take_eq, pcResults_eq, hres, seqScoped_eq, mapT_eq, drop_eq, add_leaf,
    seqHyps_eq, seqConcl_eq, eqSubst_eq, equalTs_eq, and_eq, ofBool_label, PartialHorn.inst]
  rw [hts, c2, c3, c4]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> rfl

/-- The mirror's test of a node's rule and number of children. -/
@[simp] theorem pShape_eq (l k a b : ℕ) :
    «PartialHorn.pShape» (leaf l) (leaf k) (leaf a) (leaf b) = ofBool (l == a && k == b) :=
  by simp [«PartialHorn.pShape»]

/-- The mirror's rule of the checker at a node is the Lean checker's, at related premises. -/
theorem pcheckStep_eq (T : PartialHorn.Theory) (E : Array PartialHorn.Seq) (l : ℕ)
    (xs : List (Tree × (List Tree → List Tree → Tree) × PartialHorn.Chk))
    (hx : ∀ x ∈ xs, ChkRel x.2.1 x.2.2) :
    ChkRel («PartialHorn.pcheckStep» (encTheory T) (E.toList.map encSeq) (leaf l)
        («PartialHorn.pcTrees» (xs.map fun x ↦ (x.1, x.2.1))) (xs.map fun x ↦ (x.1, x.2.1)))
      (PartialHorn.checkStep T E l (xs.map fun x ↦ (x.1, x.2.2))) := by
  intro Γ H
  simp only [«PartialHorn.pcheckStep», pcTrees_eq, List.map_map, Function.comp_def,
    length_eq, List.length_map, at_eq, pShape_eq]
  have hx0 := fun x (h : x ∈ xs) ↦ hx x h Γ H
  rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | l
  · -- a hypothesis
    rcases xs with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp only [BEq.rfl, List.length_nil, Nat.reduceBEq,
        Bool.and_false, ne_eq, ofBool_label, Bool.false_eq_true, ↓reduceIte, Bool.and_self, eq_leaf,
        lt_leaf, lt_self_iff_false, decide_false, and_eq, none_eq, PartialHorn.checkStep,
        List.map_nil, Option.map_none, List.length_cons, zero_add, List.map_cons,
        List.getD_eq_getElem?_getD, zero_lt_one, getElem?_pos, List.getElem_cons_zero,
        Option.getD_some, leafIndex_eq, bindO_eq, Option.elim_map, Option.map_bind,
        Function.comp_apply, Nat.reduceBeqDiff, length_beq_zero, Bool.false_and,
        Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, decide_true, Bool.and_true]
    cases PartialHorn.leafIndex x.1 <;> simp [Function.comp_def, List.getElem?_map]
  · -- reflexivity
    rcases xs with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp only [zero_add, Nat.reduceBEq, List.length_nil,
        Bool.and_self, ne_eq, ofBool_label, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Bool.and_false,
        eq_leaf, lt_leaf, lt_self_iff_false, decide_false, and_eq, none_eq, PartialHorn.checkStep,
        List.map_nil, Option.map_none, List.length_cons, Bool.and_true, List.map_cons,
        List.getD_eq_getElem?_getD, zero_lt_one, getElem?_pos, List.getElem_cons_zero,
        Option.getD_some, leafIndex_eq, eqn_eq, some_eq, ite_not, bindO_eq, Option.elim_map,
        Option.map_bind, Function.comp_apply, Option.map_ite, Nat.reduceBeqDiff, length_beq_zero,
        Bool.false_and, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, decide_true]
    cases PartialHorn.leafIndex x.1 with
    | none => rfl
    | some i => by_cases h : i < Γ.length <;> simp [h, ofBool]
  · -- symmetry
    rcases xs with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp only [List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, zero_add, Nat.reduceAdd, Nat.reduceBEq, List.length_nil, Bool.and_self, ne_eq,
        ofBool_label, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Bool.and_false, eq_leaf, lt_leaf,
        lt_self_iff_false, decide_false, and_eq, none_eq, PartialHorn.checkStep, List.map_nil,
        Option.map_none, List.mem_cons, or_false, forall_eq, List.length_cons, Bool.and_true,
        eqn_eq, List.map_cons, pcPrem_eq, zero_lt_one, getElem?_pos, List.getElem_cons_zero,
        Option.map_some, Option.getD_some, Option.map_map, forall_eq_or_imp, Prod.forall,
        Nat.reduceBeqDiff, length_beq_zero, Bool.false_and, Nat.lt_add_left_iff_pos,
        Nat.zero_lt_succ, decide_true] at hx0 ⊢
    rw [hx0]
    simp [Option.map_map, Function.comp_def]
  · -- transitivity
    rcases xs with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;>
      simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, zero_add, Nat.reduceAdd,
          Nat.reduceBEq, List.length_nil, Bool.and_self, ne_eq, ofBool_label, Bool.false_eq_true,
          ↓reduceIte, BEq.rfl, Bool.and_false, eq_leaf, lt_leaf, lt_self_iff_false, decide_false,
          and_eq, none_eq, PartialHorn.checkStep, List.map_nil, Option.map_none, List.mem_cons,
          or_false, forall_eq, List.length_cons, Bool.and_true, zero_lt_one, decide_true,
          List.map_cons, forall_eq_or_imp, pcPrem_eq, Nat.zero_lt_succ, getElem?_pos,
          List.getElem_cons_zero, Option.map_some, Option.getD_some, Nat.lt_add_one,
          List.getElem_cons_succ, equal_eq, decide_eq_true_eq, eqn_eq, some_eq, Option.map_bind,
          Function.comp_apply, Option.map_ite, Prod.forall, Nat.reduceBeqDiff,
          Nat.lt_add_left_iff_pos] at hx0 ⊢
    rw [hx0.1, hx0.2]
    cases x.2.2 Γ H <;> cases y.2.2 Γ H <;> simp
    split <;> rfl
  · -- congruence
    rcases xs with _ | ⟨x, r⟩
    · rfl
    have hr : (r.map fun x ↦ (x.1, x.2.1)).map (fun r ↦ r.2 (Γ.map leaf) (H.map encEqn)) =
        r.map fun x ↦ encOpt ((x.2.2 Γ H).map encEqn) := by
      simp only [List.map_map, Function.comp_def]
      exact List.map_congr_left fun y h ↦ hx y (List.mem_cons_of_mem x h) Γ H
    simp only [List.map_cons, pcTail_eq, List.tail_cons, pcResults_eq, hr]
    simp only [zero_add, Nat.reduceAdd, Nat.reduceBEq, List.length_cons, Nat.reduceBeqDiff,
        length_beq_zero, Bool.false_and, ne_eq, ofBool_label, Bool.false_eq_true, ↓reduceIte,
        eq_leaf, BEq.rfl, lt_leaf, Nat.zero_lt_succ, decide_true, and_eq, Bool.and_self, pcPrem_eq,
        List.length_map, getElem?_pos, List.getElem_cons_zero, Option.map_some, Option.getD_some,
        hx x List.mem_cons_self Γ H, label_eq, not_eq, mapT_eq, List.map_map, children_eq,
        equalTs_eq, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
        decide_eq_true_eq, node_leaf, eqn_eq, none_eq, bindO_eq, Option.elim_map,
        PartialHorn.checkStep, List.mapM_map, Option.map_bind, Function.comp_apply]
    cases x.2.2 Γ H with
    | none => rfl
    | some q =>
      simp only [Function.comp_def, mapO_eq, Option.map_map, eqLhs_eq, eqRhs_eq, Option.elim_some,
          Option.bind_some]
      have hc : (r.map fun x ↦ encOpt ((x.2.2 Γ H).map PartialHorn.Eqn.lhs)) =
            q.lhs.children.map (fun t ↦ «Prelude.some» t) ↔
          r.map (fun x ↦ (x.2.2 Γ H).map PartialHorn.Eqn.lhs) = q.lhs.children.map some := by
        rw [← (List.map_injective_iff.mpr encOpt_injective).eq_iff]
        simp only [List.map_map, Function.comp_def, some_eq]
      have hs := allSomeT_eq (fun x ↦ (x.2.2 Γ H).map PartialHorn.Eqn.rhs) r
      simp only [hc, hs, mapO_eq, Option.map_map, Function.comp_def, RoseTree.children_node]
      split_ifs <;> simp [Function.comp_def]
  · -- strictness
    rcases xs with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;>
      simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, zero_add, Nat.reduceAdd,
          Nat.reduceBEq, List.length_nil, Bool.and_self, ne_eq, ofBool_label, Bool.false_eq_true,
          ↓reduceIte, eq_leaf, lt_leaf, lt_self_iff_false, decide_false, and_eq, BEq.rfl,
          Bool.and_false, none_eq, PartialHorn.checkStep, List.map_nil, Option.map_none,
          List.mem_cons, or_false, forall_eq, List.length_cons, Bool.and_true, zero_lt_one,
          decide_true, List.map_cons, forall_eq_or_imp, Nat.zero_lt_succ,
          List.getD_eq_getElem?_getD, getElem?_pos, List.getElem_cons_zero, Option.getD_some,
          leafIndex_eq, pcPrem_eq, Nat.lt_add_one, List.getElem_cons_succ, Option.map_some,
          label_eq, not_eq, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, eqn_eq,
          children_eq, ite_not, bindO_eq, Option.elim_map, Option.map_bind, Function.comp_apply,
          Prod.forall, Nat.reduceBeqDiff, Nat.lt_add_left_iff_pos] at hx0 ⊢
    rw [hx0.2]
    cases PartialHorn.leafIndex x.1 <;> cases y.2.2 Γ H <;> simp [Function.comp_def]
    split <;> simp [Function.comp_def]
  · -- an axiom
    rcases xs with _ | ⟨x, r⟩
    · rfl
    simp only [List.map_cons, pcTail_eq, List.tail_cons]
    simp only [zero_add, Nat.reduceAdd, Nat.reduceBEq, List.length_cons, Nat.reduceBeqDiff,
        length_beq_zero, Bool.false_and, ne_eq, ofBool_label, Bool.false_eq_true, ↓reduceIte,
        eq_leaf, lt_leaf, Nat.zero_lt_succ, decide_true, and_eq, Bool.and_true, BEq.rfl,
        Bool.and_self, List.getD_eq_getElem?_getD, List.length_map, getElem?_pos,
        List.getElem_cons_zero, Option.getD_some, leafIndex_eq, thyAxioms_eq, thySig_eq, bindO_eq,
        Option.elim_map, PartialHorn.checkStep, Option.map_bind, Function.comp_apply]
    cases PartialHorn.leafIndex x.1 with
    | none => rfl
    | some j =>
      simp only [Function.comp_def, nth_eq, List.getElem?_map, bindO_eq, Option.elim_map,
          Option.elim_some, Option.bind_some]
      cases T.axioms[j]? with
      | none => rfl
      | some a => exact inst_eq T.sig a r (fun y h ↦ hx y (List.mem_cons_of_mem x h)) Γ H
  · -- a cut
    rcases xs with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;>
      simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, zero_add, Nat.reduceAdd,
          Nat.reduceBEq, List.length_nil, Bool.and_self, ne_eq, ofBool_label, Bool.false_eq_true,
          ↓reduceIte, eq_leaf, lt_leaf, lt_self_iff_false, decide_false, and_eq, BEq.rfl,
          Bool.and_false, none_eq, PartialHorn.checkStep, List.map_nil, Option.map_none,
          List.mem_cons, or_false, forall_eq, List.length_cons, Bool.and_true, zero_lt_one,
          decide_true, List.map_cons, forall_eq_or_imp, Nat.zero_lt_succ, pcPrem_eq, getElem?_pos,
          List.getElem_cons_zero, Option.map_some, Option.getD_some, Nat.lt_add_one,
          List.getElem_cons_succ, Option.map_bind, Function.comp_apply, Prod.forall,
          Nat.reduceBeqDiff, Nat.lt_add_left_iff_pos] at hx0 ⊢
    rw [hx0.1]
    cases h : x.2.2 Γ H with
    | none => rfl
    | some q => exact hx y (by simp) Γ (q :: H)
  · -- a theorem
    rcases xs with _ | ⟨x, r⟩
    · rfl
    simp only [List.map_cons, pcTail_eq, List.tail_cons]
    simp only [zero_add, Nat.reduceAdd, Nat.reduceBEq, List.length_cons, Nat.reduceBeqDiff,
        length_beq_zero, Bool.false_and, ne_eq, ofBool_label, Bool.false_eq_true, ↓reduceIte,
        eq_leaf, lt_leaf, Nat.zero_lt_succ, decide_true, and_eq, Bool.and_true, BEq.rfl,
        Bool.and_self, List.getD_eq_getElem?_getD, List.length_map, getElem?_pos,
        List.getElem_cons_zero, Option.getD_some, leafIndex_eq, thySig_eq, bindO_eq,
        Option.elim_map, PartialHorn.checkStep, Option.map_bind, Function.comp_apply]
    cases PartialHorn.leafIndex x.1 with
    | none => rfl
    | some j =>
      simp only [Function.comp_def, nth_eq, List.getElem?_map, Array.getElem?_toList, bindO_eq,
          Option.elim_map, Option.elim_some, Option.bind_some]
      cases E[j]? with
      | none => rfl
      | some a => exact inst_eq T.sig a r (fun y h ↦ hx y (List.mem_cons_of_mem x h)) Γ H
  · -- no rule
    rcases xs with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp [PartialHorn.checkStep, none_eq]

/-- The mirror's checker is the Lean checker: at every certificate, its result at an encoded
context and hypotheses is the encoding of the Lean checker's. -/
theorem pcheck_eq (T : PartialHorn.Theory) (E : Array PartialHorn.Seq) (c : Tree) :
    ChkRel («PartialHorn.pcheck» (encTheory T) (E.toList.map encSeq) c)
      (PartialHorn.check T E c) := by
  simp only [«PartialHorn.pcheck», PartialHorn.check]
  apply fold_pair_snd ChkRel
  · intro l rs
    simp
  intro l xs hx
  exact pcheckStep_eq T E l xs hx

/-- The mirror's arguments' sorts of a definition. -/
@[simp] theorem pdCtx_eq (d : PartialHorn.Defn) :
    «PartialHorn.pdCtx» (encDefn d) = d.ctx.map leaf := by
  simp [«PartialHorn.pdCtx», encDefn]

/-- The mirror's sort of a definition. -/
@[simp] theorem pdSort_eq (d : PartialHorn.Defn) :
    «PartialHorn.pdSort» (encDefn d) = leaf d.sort := by
  simp [«PartialHorn.pdSort», encDefn]

/-- The mirror's body of a definition. -/
@[simp] theorem pdBody_eq (d : PartialHorn.Defn) :
    «PartialHorn.pdBody» (encDefn d) = d.body := by
  simp [«PartialHorn.pdBody», encDefn]

/-- The mirror's application of an operation to the first variables. -/
@[simp] theorem opVars_eq (n m : ℕ) :
    «PartialHorn.opVars» (leaf n) (leaf m) = PartialHorn.opVars n m := by
  simp [«PartialHorn.opVars», «PartialHorn.phOp», PartialHorn.opVars, PartialHorn.op,
    List.map_map, Function.comp_def]

/-- The mirror's axioms of a definition. -/
@[simp] theorem pdAxioms_eq (n : ℕ) (d : PartialHorn.Defn) :
    «PartialHorn.pdAxioms» (leaf n) (encDefn d) = (d.axioms n).map encSeq := by
  simp only [«PartialHorn.pdAxioms», pdCtx_eq, length_eq, List.length_map, opVars_eq,
    pdBody_eq, single_eq, eqn_eq, PartialHorn.Defn.axioms, List.map_cons, List.map_nil]
  rfl

/-- The mirror's extension of a theory by a definition. -/
@[simp] theorem thyExtend_eq (T : PartialHorn.Theory) (d : PartialHorn.Defn) :
    «PartialHorn.thyExtend» (encTheory T) (encDefn d) = encTheory (T.extend d) := by
  simp only [«PartialHorn.thyExtend», thySig_eq, thyAxioms_eq, length_eq, List.length_map,
    pdAxioms_eq, pdCtx_eq, pdSort_eq, single_eq, append_eq, PartialHorn.Theory.extend,
    PartialHorn.Sig.extend]
  simp only [encTheory, List.map_append, List.map_cons, List.map_nil]
  rfl

/-- The mirror's extension of a theory by a list of definitions, in order. -/
theorem thyExtendAll_eq (T : PartialHorn.Theory) (ds : List PartialHorn.Defn) :
    «PartialHorn.thyExtendAll» (encTheory T) (ds.map encDefn) =
      encTheory (T.extendAll ds) := by
  have h : ∀ l : List PartialHorn.Defn,
      (l.map encDefn).foldr (fun x y ↦ «PartialHorn.thyExtend» y x) (encTheory T) =
        encTheory (l.foldr (fun d T ↦ T.extend d) T) :=
    List.rec rfl fun d l ih ↦ by
      rw [List.map_cons, List.foldr_cons, ih, List.foldr_cons, thyExtend_eq]
  simp only [«PartialHorn.thyExtendAll», foldr_eq, reverse_eq, ← List.map_reverse,
    PartialHorn.Theory.extendAll, List.foldl_eq_foldr_reverse]
  exact h ds.reverse

end GebTests.Prototypes.FreeTopos.Agreement.PartialHorn

end
