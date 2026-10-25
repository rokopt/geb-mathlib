/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelContext
import Geb.Prototypes.InteractionNet.KernelValueShape
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Represented kernel constructor rules

The generic dispatch theorem specializes to canonical tree values. Rule proofs can then
work with expressions for the original children and additional arguments, leaving wire
allocation, copying, and equation scheduling to contextual normalization.

## Tags

interaction net, kernel, constructor, dispatch, simulation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder
open scoped FinEnum

/-- A rule on a tree is represented when its expression body preserves representation. -/
theorem callsTo_tree (P : List Tree) (f : Op) (l : ℕ) (ts args : List Tree) (result : Tree)
    (hb : ∀ {n : ℕ} (ρ : Fin n → Value dataArity) (es fs : List (E n)),
      List.Forall₂ (fun e t ↦ EvaluatesTo P ρ e (Eval.Val.quote t)) es ts →
      List.Forall₂ (EvaluatesTo P ρ) fs args →
      ∃ body, rewrite P f (.tree l ts.length) es fs = some body ∧
        EvaluatesTo P ρ body result) :
    CallsTo P f (Eval.Val.quote (RoseTree.node l ts)) args result := by
  intro v hv vs hvs
  obtain rfl := eq_treeValue_of_rep v _ hv
  rw [treeValue_node_get]
  apply calls_of_body P f (.tree l ts.length) _ vs (ts.map Eval.Val.quote) args result
  · simpa only [← Function.comp_def, ← List.map_ofFn, List.ofFn_get] using
      fields_related Rep (fun i ↦ treeValue (ts.get i))
        (fun i ↦ Eval.Val.quote (ts.get i)) (fun i ↦ rep_treeValue (ts.get i))
  · exact hvs
  · intro n ρ es fs hes hfs
    exact hb ρ es fs ((List.forall₂_map_right_iff).mp hes) hfs

/-- A numeric rule returns its computed label as a leaf and consumes the inspected tree. -/
theorem callsTo_numeric (P : List Tree) (k a b r : ℕ) (ts : List Tree)
    (h : numeric k a b = some r) :
    CallsTo P (.numeric k a) (Eval.Val.quote (RoseTree.node b ts)) []
      (Eval.Val.quote (leaf r)) := by
  apply callsTo_tree
  intro n ρ es fs _ hfs
  obtain rfl := List.forall₂_nil_right_iff.mp hfs
  refine ⟨tree r [], ?_, evaluatesTo_tree P ρ r [] [] .nil⟩
  simp only [rewrite, h, Option.map_some]

/-- Conjunction discards a false right operand or returns the represented right operand. -/
theorem callsTo_and (P : List Tree) (l : ℕ) (ts : List Tree) (b : Tree) :
    CallsTo P .and (Eval.Val.quote (RoseTree.node l ts)) [b]
      (if l = 0 then Eval.Val.quote (leaf 0) else b) := by
  apply callsTo_tree
  intro n ρ es fs _ hfs
  obtain ⟨e, tail, he, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
  obtain rfl := List.forall₂_nil_right_iff.mp ht
  refine ⟨if l = 0 then tree 0 [] else e, rfl, ?_⟩
  split
  · exact evaluatesTo_tree P ρ 0 [] [] .nil
  · exact he

/-- Pair projection returns the selected represented field. -/
theorem callsTo_project (P : List Tree) (second : Bool) (x y : Tree) :
    CallsTo P (.project second) (Eval.Val.pair x y) [] (if second then y else x) := by
  intro v hv args hargs
  obtain rfl := List.forall₂_nil_right_iff.mp hargs
  obtain ⟨vs, rfl, hx, hy⟩ := rep_pair_fields v x y hv
  have hcs : List.Forall₂ Rep (List.ofFn vs) [x, y] := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    exact .cons hx (.cons hy .nil)
  apply calls_of_body P (.project second) .pair vs [] [x, y] [] _ hcs .nil
  intro n ρ es fs hes hfs
  obtain rfl := List.forall₂_nil_right_iff.mp hfs
  obtain ⟨a, tail, ha, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hes
  obtain ⟨b, rest, hb, hr, rfl⟩ := List.forall₂_cons_right_iff.mp ht
  obtain rfl := List.forall₂_nil_right_iff.mp hr
  cases second with
  | false => exact ⟨a, rfl, ha⟩
  | true => exact ⟨b, rfl, hb⟩

/-- A rule on an empty list is represented when its expression body is represented. -/
theorem callsTo_nil (P : List Tree) (f : Op) (A : Tree) (args : List Tree) (result : Tree)
    (hb : ∀ {n : ℕ} (ρ : Fin n → Value dataArity) (fs : List (E n)),
      List.Forall₂ (EvaluatesTo P ρ) fs args →
      ∃ body, rewrite P f (.nil A) [] fs = some body ∧ EvaluatesTo P ρ body result) :
    CallsTo P f (RoseTree.node Label.nil [A]) args result := by
  intro v hv vs hvs
  obtain rfl := rep_nil_value v A hv
  apply calls_of_body P f (.nil A) Fin.elim0 vs [] args result .nil hvs
  intro n ρ es fs hes hfs
  obtain rfl := List.forall₂_nil_right_iff.mp hes
  exact hb ρ fs hfs

/-- A rule on a list cell is represented when its expression body preserves its fields. -/
theorem callsTo_cons (P : List Tree) (f : Op) (x xs : Tree) (args : List Tree) (result : Tree)
    (hb : ∀ {n : ℕ} (ρ : Fin n → Value dataArity) (e tail : E n) (fs : List (E n)),
      EvaluatesTo P ρ e x → EvaluatesTo P ρ tail xs →
      List.Forall₂ (EvaluatesTo P ρ) fs args →
      ∃ body, rewrite P f .cons [e, tail] fs = some body ∧ EvaluatesTo P ρ body result) :
    CallsTo P f (RoseTree.node Label.cons [x, xs]) args result := by
  intro v hv vs hvs
  obtain ⟨ws, rfl, hx, hxs⟩ := rep_cons_fields v x xs hv
  have hcs : List.Forall₂ Rep (List.ofFn ws) [x, xs] := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    exact .cons hx (.cons hxs .nil)
  apply calls_of_body P f .cons ws vs [x, xs] args result hcs hvs
  intro n ρ es fs hes hfs
  obtain ⟨e, tail, he, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hes
  obtain ⟨t, rest, htail, hr, rfl⟩ := List.forall₂_cons_right_iff.mp ht
  obtain rfl := List.forall₂_nil_right_iff.mp hr
  exact hb ρ e t fs he htail hfs

end Geb.InteractionNet.Kernel

end
