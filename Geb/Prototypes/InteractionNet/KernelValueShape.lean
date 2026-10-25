/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelValue
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Recovering runtime data shapes

The representation relation preserves the distinction between data constructors and
function values. In particular, a represented pair exposes two related runtime fields,
and a represented list exposes the same empty or nonempty shape as the evaluator's list.
These facts justify constructor dispatch on represented data.

## Tags

interaction net, kernel, representation, pair, list, constructor
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder

/-- A represented pair has the pair constructor and related fields in the same order. -/
theorem rep_pair_fields (v : Value dataArity) (x y : Tree) (h : Rep v (Eval.Val.pair x y)) :
    ∃ vs : Fin 2 → Value dataArity,
      v = Term.agent (.inl .pair) vs ∧ Rep (vs 0) x ∧ Rep (vs 1) y := by
  cases v with
  | pure x => exact x.elim
  | liftBind a vs =>
    cases a with
    | inr n => exact False.elim h
    | inl a =>
      cases a with
      | pair =>
        obtain ⟨x', y', hx, hy, he⟩ := h
        have hh := congrArg RoseTree.children he
        simp only [Eval.Val.pair, RoseTree.children_node, List.cons.injEq, and_true] at hh
        obtain ⟨rfl, rfl⟩ := hh
        exact ⟨vs, rfl, hx, hy⟩
      | tree =>
        obtain ⟨ts, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | unit =>
        have hh := congrArg RoseTree.label h
        exact False.elim (by cases hh)
      | nil =>
        have hh := congrArg RoseTree.label h
        exact False.elim (by cases hh)
      | cons =>
        obtain ⟨a, b, _, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | closure =>
        obtain ⟨en, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | partialApp =>
        obtain ⟨hh, args, _, he⟩ := h
        exact False.elim (hh.spine_ne (List.ofFn args) Label.pair (by decide)
          (by rw [← he]; rfl))
      | thunk => exact False.elim h

/-- A represented list cell has the list constructor and related head and tail. -/
theorem rep_cons_fields (v : Value dataArity) (x y : Tree)
    (h : Rep v (RoseTree.node Label.cons [x, y])) :
    ∃ vs : Fin 2 → Value dataArity,
      v = Term.agent (.inl .cons) vs ∧ Rep (vs 0) x ∧ Rep (vs 1) y := by
  cases v with
  | pure x => exact x.elim
  | liftBind a vs =>
    cases a with
    | inr n => exact False.elim h
    | inl a =>
      cases a with
      | cons =>
        obtain ⟨x', y', hx, hy, he⟩ := h
        have hh := congrArg RoseTree.children he
        simp only [RoseTree.children_node, List.cons.injEq, and_true] at hh
        obtain ⟨rfl, rfl⟩ := hh
        exact ⟨vs, rfl, hx, hy⟩
      | tree =>
        obtain ⟨ts, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | unit =>
        have hh := congrArg RoseTree.label h
        exact False.elim (by cases hh)
      | nil =>
        have hh := congrArg RoseTree.label h
        exact False.elim (by cases hh)
      | pair =>
        obtain ⟨a, b, _, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | closure =>
        obtain ⟨en, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | partialApp =>
        obtain ⟨hh, args, _, he⟩ := h
        exact False.elim (hh.spine_ne (List.ofFn args) Label.cons (by decide)
          (by rw [← he]; rfl))
      | thunk => exact False.elim h

/-- A represented empty list has the empty-list constructor at the same element type. -/
theorem rep_nil_value (v : Value dataArity) (A : Tree)
    (h : Rep v (RoseTree.node Label.nil [A])) :
    v = Term.agent (.inl (.nil A)) Fin.elim0 := by
  cases v with
  | pure x => exact x.elim
  | liftBind a vs =>
    cases a with
    | inr n => exact False.elim h
    | inl a =>
      cases a with
      | nil B =>
        have hh := congrArg RoseTree.children h
        simp only [RoseTree.children_node, List.cons.injEq, and_true] at hh
        subst B
        apply congrArg (Term.agent (arity := constructorArity dataArity) (.inl (.nil A)))
        exact funext fun i ↦ i.elim0
      | tree =>
        obtain ⟨ts, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | unit =>
        have hh := congrArg RoseTree.label h
        exact False.elim (by cases hh)
      | pair =>
        obtain ⟨x, y, _, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | cons =>
        obtain ⟨x, y, _, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | closure =>
        obtain ⟨en, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | partialApp =>
        obtain ⟨hh, args, _, he⟩ := h
        exact False.elim (hh.spine_ne (List.ofFn args) Label.nil (by decide)
          (by rw [← he]; rfl))
      | thunk => exact False.elim h

/-- A represented unit has the nullary unit constructor. -/
theorem rep_unit_value (v : Value dataArity) (h : Rep v Eval.Val.unit) :
    v = Term.agent (.inl .unit) Fin.elim0 := by
  cases v with
  | pure x => exact x.elim
  | liftBind a vs =>
    cases a with
    | inr n => exact False.elim h
    | inl a =>
      cases a with
      | unit =>
        apply congrArg (Term.agent (arity := constructorArity dataArity) (.inl .unit))
        exact funext fun i ↦ i.elim0
      | tree =>
        obtain ⟨ts, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | nil =>
        have hh := congrArg RoseTree.label h
        exact False.elim (by cases hh)
      | pair =>
        obtain ⟨x, y, _, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | cons =>
        obtain ⟨x, y, _, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | closure =>
        obtain ⟨en, _, he⟩ := h
        have hh := congrArg RoseTree.label he
        exact False.elim (by cases hh)
      | partialApp =>
        obtain ⟨hh, args, _, he⟩ := h
        exact False.elim (hh.spine_ne (List.ofFn args) Label.unit (by decide)
          (by rw [← he]; rfl))
      | thunk => exact False.elim h

/-- Every successfully decoded evaluator list is a list constructor chain with one final
element-type annotation. The decoder does not require the elements to be well typed. -/
theorem ofList_of_listOf (v : Tree) (xs : List Tree) (h : Eval.listOf v = some xs) :
    ∃ A, v = Eval.Val.ofList A xs := by
  apply RoseTree.ind (P := fun v ↦ ∀ xs, Eval.listOf v = some xs →
    ∃ A, v = Eval.Val.ofList A xs) (fun l cs ih xs h ↦ ?_) v xs h
  unfold Eval.listOf at h
  rw [RoseTree.para_node] at h
  split at h
  next p heq =>
    obtain ⟨A, r⟩ := p
    obtain ⟨rfl, _⟩ := Eval.map_pair_eq_one heq
    obtain rfl := Option.some.inj h
    exact ⟨A, rfl⟩
  next x _ tail r heq =>
    obtain ⟨rfl, _, rfl⟩ := Eval.map_pair_eq_two heq
    obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨A, hA⟩ := ih tail (by simp) ys hys
    exact ⟨A, congrArg (fun t ↦ RoseTree.node Label.cons [x, t]) hA⟩
  next => cases h

end Geb.InteractionNet.Kernel

end
