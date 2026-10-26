/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelRecursors
import Geb.Prototypes.InteractionNet.KernelPrimitives
import Mathlib.Data.List.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Saturated kernel constants

A fully supplied kernel constant dispatches to one recursion or primitive operation. The
evaluator checks its head, type-argument count, and value-argument count. Each successful
case translates to an expression whose contextual execution represents the same result.

## Main statements

* {lit}`saturated_evaluatesTo` — successful evaluator dispatch is preserved by translation.

## Tags

interaction net, kernel, constant, saturation, application, simulation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder

/-- Saturating represented arguments produces a represented expression whenever the
evaluator's saturation succeeds and its function applications are simulated. -/
theorem saturated_evaluatesTo (P : List Tree) (ap : Tree → Tree → Option Tree)
    (ha : ApplicationSimulation P ap) {n : ℕ} (ρ : Fin n → Value dataArity)
    (site : List ℕ) (hd : Tree) (es : List (E n)) (args : List Tree) (result : Tree)
    (hes : List.Forall₂ (EvaluatesTo P ρ) es args) (h : Eval.sat ap hd args = some result) :
    ∃ e, saturated site hd es = some e ∧ EvaluatesTo P ρ e result := by
  unfold Eval.sat at h
  dsimp only at h
  split_ifs at h with hfold hpara hiter hfoldr hlcase hprim₂ hnode hprim₁
  · obtain ⟨A, hA⟩ := List.length_eq_one_iff.mp hfold.2.1
    obtain ⟨f, x, rfl⟩ := List.length_eq_two.mp hfold.2.2
    have hh : hd = RoseTree.node Label.fold [A] :=
      (RoseTree.node_eq_iff.mpr ⟨hfold.1.symm, hA.symm⟩).symm
    subst hd
    change (Eval.unquote x).bind (Eval.foldVal ap A f) = some result at h
    obtain ⟨t, ht, hr⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := eq_quote_of_unquote x t ht
    obtain ⟨e, tail, he, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hes
    obtain ⟨ex, rest, hx, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp htail
    obtain rfl := List.forall₂_nil_right_iff.mp hrest
    exact ⟨call (.fold site A) ex [e], rfl,
      evaluatesTo_call P ρ (.fold site A) ex [e] (Eval.Val.quote t) result [f]
        hx (.cons he .nil) (callsTo_fold P ap ha site A f t result hr)⟩
  · obtain ⟨A, hA⟩ := List.length_eq_one_iff.mp hpara.2.1
    obtain ⟨f, x, rfl⟩ := List.length_eq_two.mp hpara.2.2
    have hh : hd = RoseTree.node Label.para [A] :=
      (RoseTree.node_eq_iff.mpr ⟨hpara.1.symm, hA.symm⟩).symm
    subst hd
    change (Eval.unquote x).bind (Eval.paraVal ap A f) = some result at h
    obtain ⟨t, ht, hr⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := eq_quote_of_unquote x t ht
    obtain ⟨e, tail, he, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hes
    obtain ⟨ex, rest, hx, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp htail
    obtain rfl := List.forall₂_nil_right_iff.mp hrest
    exact ⟨call (.para site A) ex [e], rfl,
      evaluatesTo_call P ρ (.para site A) ex [e] (Eval.Val.quote t) result [f]
        hx (.cons he .nil) (callsTo_para P ap ha site A f t result hr)⟩
  · obtain ⟨A, hA⟩ := List.length_eq_one_iff.mp hiter.2.1
    obtain ⟨s, z, x, rfl⟩ := List.length_eq_three.mp hiter.2.2
    have hh : hd = RoseTree.node Label.iter [A] :=
      (RoseTree.node_eq_iff.mpr ⟨hiter.1.symm, hA.symm⟩).symm
    subst hd
    change (Eval.unquote x).bind (fun t ↦ Eval.iterVal ap s z t.label) = some result at h
    obtain ⟨t, ht, hr⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := eq_quote_of_unquote x t ht
    obtain ⟨e, tail, he, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hes
    obtain ⟨ez, rest, hz, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp htail
    obtain ⟨ex, rest', hx, hrest', rfl⟩ := List.forall₂_cons_right_iff.mp hrest
    obtain rfl := List.forall₂_nil_right_iff.mp hrest'
    have hc : CallsTo P (.iter site) (Eval.Val.quote t) [s, z] result := by
      simpa only [RoseTree.node_label_children] using
        callsTo_iter P ap ha site s z t.label t.children result hr
    exact ⟨call (.iter site) ex [e, ez], rfl,
      evaluatesTo_call P ρ (.iter site) ex [e, ez] (Eval.Val.quote t) result [s, z]
        hx (.cons he (.cons hz .nil)) hc⟩
  · obtain ⟨A, B, hAB⟩ := List.length_eq_two.mp hfoldr.2.1
    obtain ⟨f, z, xs, rfl⟩ := List.length_eq_three.mp hfoldr.2.2
    have hh : hd = RoseTree.node Label.foldr [A, B] :=
      (RoseTree.node_eq_iff.mpr ⟨hfoldr.1.symm, hAB.symm⟩).symm
    subst hd
    change (Eval.listOf xs).bind (Eval.foldrVal ap f z) = some result at h
    obtain ⟨vs, hvs, hr⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, tail, he, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hes
    obtain ⟨ez, rest, hz, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp htail
    obtain ⟨ex, rest', hx, hrest', rfl⟩ := List.forall₂_cons_right_iff.mp hrest
    obtain rfl := List.forall₂_nil_right_iff.mp hrest'
    exact ⟨call (.foldr site) ex [e, ez], rfl,
      evaluatesTo_call P ρ (.foldr site) ex [e, ez] xs result [f, z]
        hx (.cons he (.cons hz .nil)) (callsTo_foldr P ap ha site f z xs vs result hvs hr)⟩
  · obtain ⟨A, B, hAB⟩ := List.length_eq_two.mp hlcase.2.1
    obtain ⟨xs, z, f, rfl⟩ := List.length_eq_three.mp hlcase.2.2
    have hh : hd = RoseTree.node Label.lcase [A, B] :=
      (RoseTree.node_eq_iff.mpr ⟨hlcase.1.symm, hAB.symm⟩).symm
    subst hd
    change Eval.lcaseVal ap xs z f = some result at h
    obtain ⟨ex, tail, hx, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hes
    obtain ⟨ez, rest, hz, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp htail
    obtain ⟨e, rest', he, hrest', rfl⟩ := List.forall₂_cons_right_iff.mp hrest
    obtain rfl := List.forall₂_nil_right_iff.mp hrest'
    exact ⟨call .lcase ex [ez, e], rfl,
      evaluatesTo_call P ρ .lcase ex [ez, e] xs result [z, f]
        hx (.cons hz (.cons he .nil)) (callsTo_lcase P ap ha xs z f result h)⟩
  · obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp hprim₂.2.1
    obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hprim₂.2.2
    have hh : hd = RoseTree.node Label.prim [k] :=
      (RoseTree.node_eq_iff.mpr ⟨hprim₂.1.symm, hk.symm⟩).symm
    subst hd
    change Eval.primNode x y = some result at h
    change k.label = Prim.node at hnode
    obtain ⟨ex, tail, hx, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hes
    obtain ⟨ey, rest, hy, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp htail
    obtain rfl := List.forall₂_nil_right_iff.mp hrest
    refine ⟨call (.primitive k.label) ex [ey], rfl, ?_⟩
    rw [hnode]
    exact evaluatesTo_call P ρ (.primitive Prim.node) ex [ey] x result [y] hx (.cons hy .nil)
      (callsTo_node P x y result h)
  · obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp hprim₂.2.1
    obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hprim₂.2.2
    have hh : hd = RoseTree.node Label.prim [k] :=
      (RoseTree.node_eq_iff.mpr ⟨hprim₂.1.symm, hk.symm⟩).symm
    subst hd
    change Eval.primApply k.label [x, y] = some result at h
    obtain ⟨ex, tail, hx, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hes
    obtain ⟨ey, rest, hy, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp htail
    obtain rfl := List.forall₂_nil_right_iff.mp hrest
    exact ⟨call (.primitive k.label) ex [ey], rfl,
      evaluatesTo_call P ρ (.primitive k.label) ex [ey] x result [y] hx (.cons hy .nil)
        (callsTo_primitive P k.label x [y] result h)⟩
  · obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp hprim₁.2.1
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hprim₁.2.2
    have hh : hd = RoseTree.node Label.prim [k] :=
      (RoseTree.node_eq_iff.mpr ⟨hprim₁.1.symm, hk.symm⟩).symm
    subst hd
    change Eval.primApply k.label [x] = some result at h
    obtain ⟨ex, tail, hx, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hes
    obtain rfl := List.forall₂_nil_right_iff.mp htail
    exact ⟨call (.primitive k.label) ex [], rfl,
      evaluatesTo_call P ρ (.primitive k.label) ex [] x result [] hx .nil
        (callsTo_primitive P k.label x [] result h)⟩

end Geb.InteractionNet.Kernel

end
