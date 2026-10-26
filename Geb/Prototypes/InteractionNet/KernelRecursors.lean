/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelContext
import Geb.Prototypes.InteractionNet.KernelRules
import Geb.Prototypes.InteractionNet.KernelValueShape
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Simulation of kernel recursion operations

The kernel's recursive operations construct further first-order calls. Their simulation
proofs follow the recursion in the existing evaluator, assuming that successful function
applications at the current evaluator level already have represented net executions.

## Main definitions

* {lit}`ApplicationSimulation` — represented execution of successful evaluator applications.

## Tags

interaction net, kernel, simulation, iteration, fold, recursion
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder

/-- Every successful application of an evaluator function has a represented net execution. -/
def ApplicationSimulation (P : List Tree) (ap : Tree → Tree → Option Tree) : Prop :=
  ∀ f x y, ap f x = some y → CallsTo P .apply f [x] y

/-- Label iteration is simulated by repeated constructor dispatch and represented application. -/
theorem callsTo_iter (P : List Tree) (ap : Tree → Tree → Option Tree)
    (ha : ApplicationSimulation P ap) (site : List ℕ) (s z : Tree) (k : ℕ)
    (ts : List Tree) (result : Tree) (h : Eval.iterVal ap s z k = some result) :
    CallsTo P (.iter site) (Eval.Val.quote (RoseTree.node k ts)) [s, z] result := by
  apply Nat.rec (motive := fun k ↦ ∀ ts result, Eval.iterVal ap s z k = some result →
    CallsTo P (.iter site) (Eval.Val.quote (RoseTree.node k ts)) [s, z] result)
    (fun ts result h ↦ ?_) (fun k ih ts result h ↦ ?_) k ts result h
  · obtain rfl := Option.some.inj h
    apply callsTo_tree
    intro n ρ es fs _ hfs
    obtain ⟨f, tail, _, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
    obtain ⟨e, rest, he, hr, rfl⟩ := List.forall₂_cons_right_iff.mp ht
    obtain rfl := List.forall₂_nil_right_iff.mp hr
    exact ⟨e, rfl, he⟩
  · change (Eval.iterVal ap s z k).bind (ap s) = some result at h
    obtain ⟨v, hv, hresult⟩ := Option.bind_eq_some_iff.mp h
    apply callsTo_tree
    intro n ρ es fs _ hfs
    obtain ⟨f, tail, hf, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
    obtain ⟨e, rest, he, hr, rfl⟩ := List.forall₂_cons_right_iff.mp ht
    obtain rfl := List.forall₂_nil_right_iff.mp hr
    refine ⟨apply f (call (.iter site) (tree k []) [f, e]), ?_, ?_⟩
    · simp only [rewrite, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
    · apply evaluatesTo_apply P ρ f _ s v result hf
      · exact evaluatesTo_call P ρ (.iter site) (tree k []) [f, e]
          (Eval.Val.quote (leaf k)) v [s, z]
          (evaluatesTo_tree P ρ k [] [] .nil) (.cons hf (.cons he .nil))
          (ih [] v hv)
      · exact ha s v result hresult

private theorem evaluatesTo_recursive_list (P : List Tree) {n : ℕ}
    (ρ : Fin n → Value dataArity) (op : Op) (A : Tree) (e : E n) (f : Tree)
    (es : List (E n)) (ts vs : List Tree) (R : Tree → Tree → Prop)
    (he : EvaluatesTo P ρ e f)
    (hes : List.Forall₂ (fun e t ↦ EvaluatesTo P ρ e (Eval.Val.quote t)) es ts)
    (hrs : List.Forall₂ R ts vs)
    (hc : ∀ t ∈ ts, ∀ v, R t v → CallsTo P op (Eval.Val.quote t) [f] v) :
    EvaluatesTo P ρ (list A (es.map fun c ↦ call op c [e])) (Eval.Val.ofList A vs) := by
  apply evaluatesTo_list
  apply List.forall₂_of_length_eq_of_get
  · simpa only [List.length_map] using hes.length_eq.trans hrs.length_eq
  · intro i hi hj
    have hi' : i < es.length := by simpa only [List.length_map] using hi
    have hi'' : i < ts.length := by simpa only [← hes.length_eq] using hi'
    have hcall := hc (ts.get ⟨i, hi''⟩) (List.get_mem ..) (vs.get ⟨i, hj⟩)
      (hrs.get hi'' hj)
    simpa only [List.get_eq_getElem, List.getElem_map] using
      evaluatesTo_call P ρ op (es.get ⟨i, hi'⟩) [e]
        (Eval.Val.quote (ts.get ⟨i, hi''⟩)) (vs.get ⟨i, hj⟩) [f]
        (hes.get hi' hi'') (.cons he .nil) hcall

/-- Tree folds evaluate every child fold and then apply the represented step to the label
and the ordered list of child results. -/
theorem callsTo_fold (P : List Tree) (ap : Tree → Tree → Option Tree)
    (ha : ApplicationSimulation P ap) (site : List ℕ) (A f t result : Tree)
    (h : Eval.foldVal ap A f t = some result) :
    CallsTo P (.fold site A) (Eval.Val.quote t) [f] result := by
  apply RoseTree.ind (P := fun t ↦ ∀ result, Eval.foldVal ap A f t = some result →
    CallsTo P (.fold site A) (Eval.Val.quote t) [f] result)
    (fun l ts ih result h ↦ ?_) t result h
  change RoseTree.elim _ _ = _ at h
  rw [RoseTree.elim_node] at h
  change ((ts.map (Eval.foldVal ap A f)).mapM id).bind
    (fun vs ↦ (ap f (Eval.Val.quote (leaf l))).bind fun g ↦ ap g (Eval.Val.ofList A vs)) =
      some result at h
  obtain ⟨vs, hvs, hs⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨g, hg, hresult⟩ := Option.bind_eq_some_iff.mp hs
  have hrs : List.Forall₂ (fun t v ↦ Eval.foldVal ap A f t = some v) ts vs :=
    List.forall₂_map_left_iff.mp (sequence_related _ _ hvs)
  apply callsTo_tree
  intro n ρ es fs hes hfs
  obtain ⟨e, tail, he, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
  obtain rfl := List.forall₂_nil_right_iff.mp ht
  refine ⟨apply (apply e (tree l [])) (list A (es.map fun c ↦ call (.fold site A) c [e])),
    rfl, ?_⟩
  apply evaluatesTo_apply P ρ _ _ g (Eval.Val.ofList A vs) result
  · exact evaluatesTo_apply P ρ e (tree l []) f (Eval.Val.quote (leaf l)) g he
      (evaluatesTo_tree P ρ l [] [] .nil) (ha _ _ _ hg)
  · exact evaluatesTo_recursive_list P ρ (.fold site A) A e f es ts vs
      (fun t v ↦ Eval.foldVal ap A f t = some v) he hes hrs ih
  · exact ha _ _ _ hresult

/-- Paramorphisms evaluate every child recursion and pass the reconstructed original node
to the represented step. Copying the original children is handled by contextual evaluation. -/
theorem callsTo_para (P : List Tree) (ap : Tree → Tree → Option Tree)
    (ha : ApplicationSimulation P ap) (site : List ℕ) (A f t result : Tree)
    (h : Eval.paraVal ap A f t = some result) :
    CallsTo P (.para site A) (Eval.Val.quote t) [f] result := by
  apply RoseTree.ind (P := fun t ↦ ∀ result, Eval.paraVal ap A f t = some result →
    CallsTo P (.para site A) (Eval.Val.quote t) [f] result)
    (fun l ts ih result h ↦ ?_) t result h
  change RoseTree.para _ _ = _ at h
  rw [RoseTree.para_node] at h
  simp only [List.map_map, Function.comp_def, List.map_id'] at h
  change ((ts.map (Eval.paraVal ap A f)).mapM id).bind
    (fun vs ↦ (ap f (Eval.Val.quote (RoseTree.node l ts))).bind
      fun g ↦ ap g (Eval.Val.ofList A vs)) = some result at h
  obtain ⟨vs, hvs, hs⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨g, hg, hresult⟩ := Option.bind_eq_some_iff.mp hs
  have hrs : List.Forall₂ (fun t v ↦ Eval.paraVal ap A f t = some v) ts vs :=
    List.forall₂_map_left_iff.mp (sequence_related _ _ hvs)
  apply callsTo_tree
  intro n ρ es fs hes hfs
  obtain ⟨e, tail, he, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
  obtain rfl := List.forall₂_nil_right_iff.mp ht
  refine ⟨apply (apply e (tree l es)) (list A (es.map fun c ↦ call (.para site A) c [e])),
    rfl, ?_⟩
  apply evaluatesTo_apply P ρ _ _ g (Eval.Val.ofList A vs) result
  · exact evaluatesTo_apply P ρ e (tree l es) f (Eval.Val.quote (RoseTree.node l ts)) g he
      (evaluatesTo_tree P ρ l es ts hes) (ha _ _ _ hg)
  · exact evaluatesTo_recursive_list P ρ (.para site A) A e f es ts vs
      (fun t v ↦ Eval.paraVal ap A f t = some v) he hes hrs ih
  · exact ha _ _ _ hresult

/-- A right fold of a represented list follows the evaluator's right fold of its elements. -/
theorem callsTo_foldr_ofList (P : List Tree) (ap : Tree → Tree → Option Tree)
    (ha : ApplicationSimulation P ap) (site : List ℕ) (A f z : Tree) (xs : List Tree)
    (result : Tree) (h : Eval.foldrVal ap f z xs = some result) :
    CallsTo P (.foldr site) (Eval.Val.ofList A xs) [f, z] result := by
  apply List.rec (motive := fun xs ↦ ∀ result, Eval.foldrVal ap f z xs = some result →
    CallsTo P (.foldr site) (Eval.Val.ofList A xs) [f, z] result)
    (fun result h ↦ ?_) (fun x xs ih result h ↦ ?_) xs result h
  · obtain rfl := Option.some.inj h
    apply callsTo_nil
    intro n ρ fs hfs
    obtain ⟨g, tail, _, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
    obtain ⟨e, rest, he, hr, rfl⟩ := List.forall₂_cons_right_iff.mp ht
    obtain rfl := List.forall₂_nil_right_iff.mp hr
    exact ⟨e, rfl, he⟩
  · change (Eval.foldrVal ap f z xs).bind
      (fun v ↦ (ap f x).bind fun g ↦ ap g v) = some result at h
    obtain ⟨v, hv, hs⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨g, hg, hresult⟩ := Option.bind_eq_some_iff.mp hs
    apply callsTo_cons
    intro n ρ e tail fs he htail hfs
    obtain ⟨f', rest, hf, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
    obtain ⟨z', rest', hz, hr, rfl⟩ := List.forall₂_cons_right_iff.mp ht
    obtain rfl := List.forall₂_nil_right_iff.mp hr
    refine ⟨apply (apply f' e) (call (.foldr site) tail [f', z']), rfl, ?_⟩
    apply evaluatesTo_apply P ρ _ _ g v result
    · exact evaluatesTo_apply P ρ f' e f x g hf he (ha _ _ _ hg)
    · exact evaluatesTo_call P ρ (.foldr site) tail [f', z'] (Eval.Val.ofList A xs) v [f, z]
        htail (.cons hf (.cons hz .nil)) (ih v hv)
    · exact ha _ _ _ hresult

/-- Every successfully decoded evaluator list has a represented right-fold execution. -/
theorem callsTo_foldr (P : List Tree) (ap : Tree → Tree → Option Tree)
    (ha : ApplicationSimulation P ap) (site : List ℕ) (f z xs : Tree) (vs : List Tree)
    (result : Tree) (hxs : Eval.listOf xs = some vs)
    (h : Eval.foldrVal ap f z vs = some result) :
    CallsTo P (.foldr site) xs [f, z] result := by
  obtain ⟨A, rfl⟩ := ofList_of_listOf xs vs hxs
  exact callsTo_foldr_ofList P ap ha site A f z vs result h

/-- List case analysis selects the empty branch or applies the represented handler to
the represented head and tail. -/
theorem callsTo_lcase (P : List Tree) (ap : Tree → Tree → Option Tree)
    (ha : ApplicationSimulation P ap) (xs z f result : Tree)
    (h : Eval.lcaseVal ap xs z f = some result) : CallsTo P .lcase xs [z, f] result := by
  apply RoseTree.ind (P := fun xs ↦ ∀ result, Eval.lcaseVal ap xs z f = some result →
    CallsTo P .lcase xs [z, f] result) (fun l cs _ result h ↦ ?_) xs result h
  simp only [Eval.lcaseVal, RoseTree.label_node, RoseTree.children_node] at h
  split at h
  next A =>
    obtain rfl := Option.some.inj h
    apply callsTo_nil
    intro n ρ fs hfs
    obtain ⟨e, tail, he, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
    obtain ⟨f', rest, _, hr, rfl⟩ := List.forall₂_cons_right_iff.mp ht
    obtain rfl := List.forall₂_nil_right_iff.mp hr
    exact ⟨e, rfl, he⟩
  next x tail _ =>
    obtain ⟨g, hg, hresult⟩ := Option.bind_eq_some_iff.mp h
    apply callsTo_cons
    intro n ρ e t fs he ht hfs
    obtain ⟨z', rest, _, hr, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
    obtain ⟨f', rest', hf, hr', rfl⟩ := List.forall₂_cons_right_iff.mp hr
    obtain rfl := List.forall₂_nil_right_iff.mp hr'
    refine ⟨apply (apply f' e) t, rfl, ?_⟩
    exact evaluatesTo_apply P ρ (apply f' e) t g tail result
      (evaluatesTo_apply P ρ f' e f x g hf he (ha _ _ _ hg)) ht (ha _ _ _ hresult)
  next => cases h

end Geb.InteractionNet.Kernel

end
