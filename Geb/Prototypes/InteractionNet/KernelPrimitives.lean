/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelContext
import Geb.Prototypes.InteractionNet.KernelRules
import Geb.Prototypes.InteractionNet.KernelValueShape
import Geb.Prototypes.InteractionNet.KernelEquality
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Simulation of kernel primitives

Tree primitives inspect constructor attributes and transfer, construct, or compare their
fields through named calls. The proofs connect these calls to the evaluator's primitive
results. Child selection includes the out-of-range default, and tree construction consumes
the represented list of children in order.

## Tags

interaction net, kernel, primitive, tree, selection, construction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder
open scoped FinEnum

private theorem related_getD {α β : Type} (R : α → β → Prop) (a : α) (b : β) (hab : R a b)
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) (i : ℕ) :
    R (xs.getD i a) (ys.getD i b) := by
  apply List.Forall₂.rec (motive := fun xs ys _ ↦ ∀ i, R (xs.getD i a) (ys.getD i b))
    (fun _ ↦ hab) (fun h _ ih i ↦ ?_) h i
  cases i with
  | zero => exact h
  | succ i => exact ih i

/-- Child selection returns the indexed represented tree, or the zero leaf out of range. -/
theorem callsTo_select (P : List Tree) (i : ℕ) (is ts : List Tree) :
    CallsTo P .select (Eval.Val.quote (RoseTree.node i is)) (ts.map Eval.Val.quote)
      (Eval.Val.quote (ts.getD i (leaf 0))) := by
  apply callsTo_tree
  intro n ρ es fs _ hfs
  refine ⟨(fs[i]?).getD (tree 0 []), rfl, ?_⟩
  exact related_getD (fun e t ↦ EvaluatesTo P ρ e (Eval.Val.quote t)) (tree 0 []) (leaf 0)
    (evaluatesTo_tree P ρ 0 [] [] .nil) (List.forall₂_map_right_iff.mp hfs) i

/-- Prepending a represented child to a represented node preserves the child order. -/
theorem callsTo_prepend (P : List Tree) (l : ℕ) (ts : List Tree) (x : Tree) :
    CallsTo P .prepend (Eval.Val.quote (RoseTree.node l ts)) [Eval.Val.quote x]
      (Eval.Val.quote (RoseTree.node l (x :: ts))) := by
  apply callsTo_tree
  intro n ρ es fs hes hfs
  obtain ⟨e, tail, he, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
  obtain rfl := List.forall₂_nil_right_iff.mp ht
  exact ⟨tree l (e :: es), rfl, evaluatesTo_tree P ρ l _ _ (.cons he hes)⟩

/-- Tree construction consumes a represented list of quoted children. -/
theorem callsTo_make_ofList (P : List Tree) (l : ℕ) (A : Tree) (ts : List Tree) :
    CallsTo P (.make l) (Eval.Val.ofList A (ts.map Eval.Val.quote)) []
      (Eval.Val.quote (RoseTree.node l ts)) := by
  apply List.rec (motive := fun ts ↦
    CallsTo P (.make l) (Eval.Val.ofList A (ts.map Eval.Val.quote)) []
      (Eval.Val.quote (RoseTree.node l ts))) ?_ (fun t ts ih ↦ ?_) ts
  · apply callsTo_nil
    intro n ρ fs hfs
    obtain rfl := List.forall₂_nil_right_iff.mp hfs
    exact ⟨tree l [], rfl, evaluatesTo_tree P ρ l [] [] .nil⟩
  · apply callsTo_cons
    intro n ρ e tail fs he ht hfs
    obtain rfl := List.forall₂_nil_right_iff.mp hfs
    refine ⟨call .prepend (call (.make l) tail) [e], rfl, ?_⟩
    exact evaluatesTo_call P ρ .prepend (call (.make l) tail) [e]
      (Eval.Val.quote (RoseTree.node l ts)) (Eval.Val.quote (RoseTree.node l (t :: ts)))
      [Eval.Val.quote t]
      (evaluatesTo_call P ρ (.make l) tail [] (Eval.Val.ofList A (ts.map Eval.Val.quote))
        (Eval.Val.quote (RoseTree.node l ts)) [] ht .nil ih)
      (.cons he .nil) (callsTo_prepend P l ts t)

/-- A successfully unquoted evaluator value is exactly the quotation of its result. -/
theorem eq_quote_of_unquote (v t : Tree) (h : Eval.unquote v = some t) : v = Eval.Val.quote t := by
  rw [← RoseTree.node_label_children v] at h ⊢
  generalize v.label = l, v.children = cs at h ⊢
  simp only [Eval.unquote, RoseTree.label_node, RoseTree.children_node] at h
  split at h
  next y => obtain rfl := Option.some.inj h; rfl
  next => cases h

/-- Successful unquotation of a list identifies all its values as quotations in order. -/
theorem eq_quotes_of_unquotes (vs ts : List Tree) (h : vs.mapM Eval.unquote = some ts) :
    vs = ts.map Eval.Val.quote := by
  have hs : (vs.map Eval.unquote).mapM id = some ts := by
    simpa only [List.mapM_map, Function.comp_def, id_eq] using h
  have hr : List.Forall₂ (fun v t ↦ Eval.unquote v = some t) vs ts :=
    List.forall₂_map_left_iff.mp (sequence_related _ _ hs)
  have he : List.Forall₂ Eq vs (ts.map Eval.Val.quote) :=
    List.forall₂_map_right_iff.mpr (hr.imp fun v t h ↦ eq_quote_of_unquote v t h)
  simpa only [List.forall₂_eq_eq_eq] using he

/-- Tree construction agrees with successful decoding of a list of quoted child trees. -/
theorem callsTo_make (P : List Tree) (l : ℕ) (xs : Tree) (vs ts : List Tree)
    (hxs : Eval.listOf xs = some vs) (hvs : vs.mapM Eval.unquote = some ts) :
    CallsTo P (.make l) xs [] (Eval.Val.quote (RoseTree.node l ts)) := by
  obtain rfl := eq_quotes_of_unquotes vs ts hvs
  obtain ⟨A, rfl⟩ := ofList_of_listOf xs _ hxs
  exact callsTo_make_ofList P l A ts

/-- Each successful unary primitive has the same represented constructor-rule result. -/
theorem callsTo_primitive_one (P : List Tree) (k : ℕ) (t result : Tree)
    (h : Eval.primApply k [Eval.Val.quote t] = some result) :
    CallsTo P (.primitive k) (Eval.Val.quote t) [] result := by
  rw [← RoseTree.node_label_children t] at h ⊢
  generalize t.label = l, t.children = ts at h ⊢
  change (if k = Prim.label then some (Eval.Val.quote (leaf l))
    else if k = Prim.arity then some (Eval.Val.quote (leaf ts.length))
    else if k = Prim.children then
      some (Eval.Val.ofList tT ((RoseTree.node l ts).children.map Eval.Val.quote))
    else if k = Prim.log2 then some (Eval.Val.quote (leaf l.log2)) else none) = some result at h
  rw [RoseTree.children_node] at h
  split at h
  · obtain rfl := Option.some.inj h
    apply callsTo_tree
    intro n ρ es fs _ hfs
    obtain rfl := List.forall₂_nil_right_iff.mp hfs
    exact ⟨tree l [], by subst k; rfl,
      evaluatesTo_tree P ρ l [] [] .nil⟩
  · split at h
    · obtain rfl := Option.some.inj h
      apply callsTo_tree
      intro n ρ es fs hes hfs
      obtain rfl := List.forall₂_nil_right_iff.mp hfs
      refine ⟨tree es.length [], by subst k; rfl, ?_⟩
      have he : EvaluatesTo P ρ (tree es.length []) (Eval.Val.quote (leaf es.length)) :=
        evaluatesTo_tree P ρ es.length [] [] .nil
      simpa only [hes.length_eq] using he
    · split at h
      · obtain rfl := Option.some.inj h
        apply callsTo_tree
        intro n ρ es fs hes hfs
        obtain rfl := List.forall₂_nil_right_iff.mp hfs
        exact ⟨list tT es, by subst k; rfl,
          evaluatesTo_list P ρ tT es _ (List.forall₂_map_right_iff.mpr hes)⟩
      · split at h
        · obtain rfl := Option.some.inj h
          apply callsTo_tree
          intro n ρ es fs _ hfs
          obtain rfl := List.forall₂_nil_right_iff.mp hfs
          exact ⟨tree l.log2 [], by subst k; rfl,
            evaluatesTo_tree P ρ l.log2 [] [] .nil⟩
        · cases h

private theorem primitive_two_eq (k : ℕ) (a b : Tree) :
    Eval.primApply k [Eval.Val.quote a, Eval.Val.quote b] =
      if k = Prim.child then some (Eval.Val.quote (Const.child a b))
      else if k = Prim.equal then some (Eval.Val.quote (Const.equal a b))
      else (numeric k a.label b.label).map (fun n ↦ Eval.Val.quote (leaf n)) := by
  by_cases hc : k = Prim.child
  · subst k; rfl
  by_cases he : k = Prim.equal
  · subst k; rfl
  change (if k = Prim.child then some (Eval.Val.quote (Const.child a b))
    else if k = Prim.add then some (Eval.Val.quote (Const.add a b))
    else if k = Prim.sub then some (Eval.Val.quote (Const.sub a b))
    else if k = Prim.mul then some (Eval.Val.quote (Const.mul a b))
    else if k = Prim.div then some (Eval.Val.quote (Const.div a b))
    else if k = Prim.mod then some (Eval.Val.quote (Const.mod a b))
    else if k = Prim.eq then some (Eval.Val.quote (Const.eq a b))
    else if k = Prim.lt then some (Eval.Val.quote (Const.lt a b))
    else if k = Prim.equal then some (Eval.Val.quote (Const.equal a b)) else none) = _
  simp only [hc, he, ↓reduceIte]
  unfold numeric
  split_ifs <;> simp_all only [Const.add, Const.sub, Const.mul, Const.div, Const.mod,
    Const.eq, Const.lt, ofBool, Option.map_some, Option.map_none, Option.some.injEq,
    Nat.succ_ne_self, not_false_eq_true, BEq.rfl, beq_iff_eq, decide_true,
    decide_eq_true_eq, not_lt, ↓reduceIte]
  rw [ite_eq_right (show ¬a.label < b.label from by omega)]

private theorem child_node (l : ℕ) (ts : List Tree) (i : Tree) :
    Const.child (RoseTree.node l ts) i = ts.getD i.label (leaf 0) := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i.label < ts.length
  · rw [List.getElem?_eq_getElem h]
    simp only [Const.child, RoseTree.node, h, ↓reduceDIte, List.getElem_toArray,
      Option.getD_some]
  · rw [List.getElem?_eq_none (by omega)]
    simp only [Const.child, RoseTree.node, h, ↓reduceDIte, Option.getD_none]

/-- The child primitive agrees with the kernel's indexed child operation. -/
theorem callsTo_child (P : List Tree) (t i : Tree) :
    CallsTo P (.primitive Prim.child) (Eval.Val.quote t) [Eval.Val.quote i]
      (Eval.Val.quote (Const.child t i)) := by
  rw [← RoseTree.node_label_children t, ← RoseTree.node_label_children i]
  generalize t.label = l, t.children = ts, i.label = k, i.children = is
  apply callsTo_tree
  intro n ρ es fs hes hfs
  obtain ⟨e, tail, he, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
  obtain rfl := List.forall₂_nil_right_iff.mp ht
  refine ⟨call .select e es, rfl, ?_⟩
  simpa only [child_node, RoseTree.label_node] using
    evaluatesTo_call P ρ .select e es (Eval.Val.quote (RoseTree.node k is))
      (Eval.Val.quote (ts.getD k (leaf 0))) (ts.map Eval.Val.quote) he
      (List.forall₂_map_right_iff.mpr hes) (callsTo_select P k is ts)

private theorem callsTo_primitive_numeric (P : List Tree) (k : ℕ) (a b : Tree) (r : ℕ)
    (hc : k ≠ Prim.child) (he : k ≠ Prim.equal) (h : numeric k a.label b.label = some r) :
    CallsTo P (.primitive k) (Eval.Val.quote a) [Eval.Val.quote b]
      (Eval.Val.quote (leaf r)) := by
  have hn : k ≠ Prim.node := by intro hk; subst k; cases h
  rw [← RoseTree.node_label_children a, ← RoseTree.node_label_children b]
  generalize a.label = l, a.children = ts, b.label = m, b.children = us at h ⊢
  apply callsTo_tree
  intro n ρ es fs _ hfs
  obtain ⟨e, tail, hb, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
  obtain rfl := List.forall₂_nil_right_iff.mp ht
  refine ⟨call (.numeric k l) e, ?_, ?_⟩
  · simp only [rewrite, primitive, hc, hn, he, ↓reduceIte]
  · exact evaluatesTo_call P ρ (.numeric k l) e [] (Eval.Val.quote (RoseTree.node m us))
      (Eval.Val.quote (leaf r)) [] hb .nil (callsTo_numeric P k l m r us h)

/-- Each successful binary primitive has the same represented constructor-rule result. -/
theorem callsTo_primitive_two (P : List Tree) (k : ℕ) (a b result : Tree)
    (h : Eval.primApply k [Eval.Val.quote a, Eval.Val.quote b] = some result) :
    CallsTo P (.primitive k) (Eval.Val.quote a) [Eval.Val.quote b] result := by
  rw [primitive_two_eq] at h
  by_cases hc : k = Prim.child
  · rw [ite_eq_left hc] at h
    obtain rfl := Option.some.inj h
    subst k
    exact callsTo_child P a b
  · rw [ite_eq_right hc] at h
    by_cases he : k = Prim.equal
    · rw [ite_eq_left he] at h
      obtain rfl := Option.some.inj h
      subst k
      exact callsTo_equal P a b
    · rw [ite_eq_right he] at h
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      exact callsTo_primitive_numeric P k a b r hc he hr

/-- Every successful ordinary evaluator primitive has a represented net execution. -/
theorem callsTo_primitive (P : List Tree) (k : ℕ) (x : Tree) (xs : List Tree) (result : Tree)
    (h : Eval.primApply k (x :: xs) = some result) :
    CallsTo P (.primitive k) x xs result := by
  unfold Eval.primApply at h
  obtain ⟨ts, hts, hs⟩ := Option.bind_eq_some_iff.mp h
  have he := eq_quotes_of_unquotes (x :: xs) ts hts
  cases ts with
  | nil => cases he
  | cons a tail =>
    cases tail with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact callsTo_primitive_one P k a result hs
    | cons b rest =>
      cases rest with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact callsTo_primitive_two P k a b result hs
      | cons c cs => cases hs

/-- The node primitive constructs precisely the tree decoded by the evaluator. -/
theorem callsTo_node (P : List Tree) (a xs result : Tree)
    (h : Eval.primNode a xs = some result) :
    CallsTo P (.primitive Prim.node) a [xs] result := by
  unfold Eval.primNode at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨t, ht, vs, hvs, ts, hts, rfl⟩ := h
  obtain rfl := eq_quote_of_unquote a t ht
  rw [← RoseTree.node_label_children t]
  generalize t.label = l, t.children = cs
  apply callsTo_tree
  intro n ρ es fs _ hfs
  obtain ⟨e, tail, he, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
  obtain rfl := List.forall₂_nil_right_iff.mp htail
  refine ⟨call (.make l) e, rfl, ?_⟩
  exact evaluatesTo_call P ρ (.make l) e [] xs (Eval.Val.quote (RoseTree.node l ts)) []
    he .nil (callsTo_make P l xs vs ts hvs hts)

end Geb.InteractionNet.Kernel

end
