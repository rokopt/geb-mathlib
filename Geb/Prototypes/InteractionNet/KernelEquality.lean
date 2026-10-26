/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelContext
import Geb.Prototypes.InteractionNet.KernelRules
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Recursive tree equality in interaction nets

Tree equality first compares labels and child counts. Matching constructors compare their
children in order and conjoin the resulting truth values. The proof follows the first
tree structurally, with the second tree arbitrary, so every recursive comparison is on
a strict child of the first tree.

## Tags

interaction net, kernel, equality, tree, primitive, comparison
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder
open scoped FinEnum

/-- The equality primitive returns one or zero according to tree equality. -/
theorem equal_eq_if (a b : Tree) : Const.equal a b = if a = b then leaf 1 else leaf 0 := by
  by_cases h : a = b <;> simp [Const.equal, ofBool, h]

private def compareFields {n : ℕ} (es fs : List (E n)) : E n :=
  (es.zipWith (fun e f ↦ call (.primitive Prim.equal) e [f]) fs).foldr
    (fun e acc ↦ call .and e [acc]) (tree 1 [])

private theorem evaluatesTo_compareFields (P : List Tree) {n : ℕ}
    (ρ : Fin n → Value dataArity) (ts us : List Tree) (es fs : List (E n))
    (hlen : ts.length = us.length)
    (hes : List.Forall₂ (fun e t ↦ EvaluatesTo P ρ e (Eval.Val.quote t)) es ts)
    (hfs : List.Forall₂ (fun e t ↦ EvaluatesTo P ρ e (Eval.Val.quote t)) fs us)
    (hc : ∀ t ∈ ts, ∀ u, CallsTo P (.primitive Prim.equal) (Eval.Val.quote t)
      [Eval.Val.quote u] (Eval.Val.quote (if t = u then leaf 1 else leaf 0))) :
    EvaluatesTo P ρ (compareFields es fs)
      (Eval.Val.quote (if ts = us then leaf 1 else leaf 0)) := by
  apply List.rec (motive := fun ts ↦ ∀ us es fs, ts.length = us.length →
    List.Forall₂ (fun e t ↦ EvaluatesTo P ρ e (Eval.Val.quote t)) es ts →
    List.Forall₂ (fun e t ↦ EvaluatesTo P ρ e (Eval.Val.quote t)) fs us →
    (∀ t ∈ ts, ∀ u, CallsTo P (.primitive Prim.equal) (Eval.Val.quote t)
      [Eval.Val.quote u] (Eval.Val.quote (if t = u then leaf 1 else leaf 0))) →
    EvaluatesTo P ρ (compareFields es fs)
      (Eval.Val.quote (if ts = us then leaf 1 else leaf 0)))
    (fun us es fs hlen hes hfs _ ↦ ?_)
    (fun t ts ih us es fs hlen hes hfs hc ↦ ?_) ts us es fs hlen hes hfs hc
  · obtain rfl := List.length_eq_zero_iff.mp hlen.symm
    obtain rfl := List.forall₂_nil_right_iff.mp hes
    obtain rfl := List.forall₂_nil_right_iff.mp hfs
    exact evaluatesTo_tree P ρ 1 [] [] .nil
  · cases us with
    | nil => cases hlen
    | cons u us =>
      obtain ⟨e, es', he, he', rfl⟩ := List.forall₂_cons_right_iff.mp hes
      obtain ⟨f, fs', hf, hf', rfl⟩ := List.forall₂_cons_right_iff.mp hfs
      have hh := evaluatesTo_call P ρ (.primitive Prim.equal) e [f]
        (Eval.Val.quote t) (Eval.Val.quote (if t = u then leaf 1 else leaf 0))
        [Eval.Val.quote u] he (.cons hf .nil) (hc t (List.mem_cons_self ..) u)
      have ht := ih us es' fs' (Nat.succ.inj hlen) he' hf'
        (fun t ht ↦ hc t (List.mem_cons_of_mem _ ht))
      have hand : CallsTo P .and (Eval.Val.quote (if t = u then leaf 1 else leaf 0))
          [Eval.Val.quote (if ts = us then leaf 1 else leaf 0)]
          (Eval.Val.quote (if t :: ts = u :: us then leaf 1 else leaf 0)) := by
        by_cases htu : t = u
        · simpa [htu, leaf] using
            callsTo_and P 1 [] (Eval.Val.quote (if ts = us then leaf 1 else leaf 0))
        · simpa [htu, leaf] using
            callsTo_and P 0 [] (Eval.Val.quote (if ts = us then leaf 1 else leaf 0))
      exact evaluatesTo_call P ρ .and (call (.primitive Prim.equal) e [f])
        [compareFields es' fs'] (Eval.Val.quote (if t = u then leaf 1 else leaf 0))
        (Eval.Val.quote (if t :: ts = u :: us then leaf 1 else leaf 0))
        [Eval.Val.quote (if ts = us then leaf 1 else leaf 0)] hh (.cons ht .nil) hand

private theorem callsTo_compare_of_children (P : List Tree) (l : ℕ) (ts : List Tree)
    (r : ℕ) (us : List Tree)
    (hc : ∀ t ∈ ts, ∀ u, CallsTo P (.primitive Prim.equal) (Eval.Val.quote t)
      [Eval.Val.quote u] (Eval.Val.quote (Const.equal t u))) :
    CallsTo P (.compare l ts.length) (Eval.Val.quote (RoseTree.node r us))
      (ts.map Eval.Val.quote) (Eval.Val.quote (Const.equal (RoseTree.node l ts)
        (RoseTree.node r us))) := by
  apply callsTo_tree
  intro n ρ es fs hes hfs
  have hfs' := List.forall₂_map_right_iff.mp hfs
  by_cases hm : l = r ∧ ts.length = us.length
  · obtain ⟨hr, hlen⟩ := hm
    subst r
    refine ⟨compareFields fs es, ite_eq_left ⟨rfl, hlen⟩, ?_⟩
    have hn : (RoseTree.node l ts = RoseTree.node l us) ↔ ts = us := by
      constructor
      · intro h
        simpa only [RoseTree.children_node] using congrArg RoseTree.children h
      · exact congrArg (RoseTree.node l)
    simpa only [equal_eq_if, hn] using evaluatesTo_compareFields P ρ ts us fs es hlen
      hfs' hes (fun t ht u ↦ by simpa only [equal_eq_if] using hc t ht u)
  · refine ⟨tree 0 [], ite_eq_right hm, ?_⟩
    have hn : RoseTree.node l ts ≠ RoseTree.node r us := by
      intro h
      apply hm
      constructor
      · simpa only [RoseTree.label_node] using congrArg RoseTree.label h
      · simpa only [RoseTree.children_node] using
          congrArg List.length (congrArg RoseTree.children h)
    have hz : EvaluatesTo P ρ (tree 0 []) (Eval.Val.quote (leaf 0)) :=
      evaluatesTo_tree P ρ 0 [] [] .nil
    simpa only [equal_eq_if, ite_eq_right hn] using hz

/-- Recursive constructor comparison returns the evaluator's equality result for all trees. -/
theorem callsTo_equal (P : List Tree) (t u : Tree) :
    CallsTo P (.primitive Prim.equal) (Eval.Val.quote t) [Eval.Val.quote u]
      (Eval.Val.quote (Const.equal t u)) := by
  apply RoseTree.ind (P := fun t ↦ ∀ u,
    CallsTo P (.primitive Prim.equal) (Eval.Val.quote t) [Eval.Val.quote u]
      (Eval.Val.quote (Const.equal t u))) (fun l ts ih u ↦ ?_) t u
  rw [← RoseTree.node_label_children u]
  generalize u.label = r, u.children = us
  apply callsTo_tree
  intro n ρ es fs hes hfs
  obtain ⟨e, tail, he, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hfs
  obtain rfl := List.forall₂_nil_right_iff.mp ht
  refine ⟨call (.compare l es.length) e es, rfl, ?_⟩
  have hv := evaluatesTo_call P ρ (.compare l ts.length) e es
    (Eval.Val.quote (RoseTree.node r us))
    (Eval.Val.quote (Const.equal (RoseTree.node l ts) (RoseTree.node r us)))
    (ts.map Eval.Val.quote) he (List.forall₂_map_right_iff.mpr hes)
    (callsTo_compare_of_children P l ts r us ih)
  simpa only [hes.length_eq] using hv

end Geb.InteractionNet.Kernel

end
