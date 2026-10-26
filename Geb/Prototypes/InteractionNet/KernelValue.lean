/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Observation
public import Geb.Prototypes.InteractionNet.Expression
import Geb.Prototypes.InteractionNet.Evaluation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Kernel values and evaluator values

Runtime closures retain their source paths, while the existing evaluator stores only
their code and captured environment. The representation relation forgets those paths and
relates captured fields recursively. Partial applications record their argument list in
one constructor; the evaluator records the same arguments as an application spine.

Tree literals already have canonical runtime values. Their contextual evaluation and
representation are independent of the loaded program.

## Main definitions

* {lit}`ConstantHead` — the kernel constants that can collect arguments.
* {lit}`Rep` — the relation between runtime constructor values and evaluator values.

## Tags

interaction net, kernel, value, representation, closure, literal
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder
open scoped FinEnum

/-- A constant that collects arguments before its kernel operation is dispatched. -/
def ConstantHead (h : Tree) : Prop :=
  h.label = Label.fold ∨ h.label = Label.para ∨ h.label = Label.iter ∨
    h.label = Label.foldr ∨ h.label = Label.lcase ∨ h.label = Label.prim

/-- Runtime values represent evaluator values after forgetting source paths and expanding
partial applications into application spines. Thunks and environment nodes are internal. -/
def Rep : Value dataArity → Tree → Prop :=
  PFunctor.FreeM.rec Empty.elim fun a _ rs ↦
    match a with
    | .inr _ => fun _ ↦ False
    | .inl a => match a with
      | .tree l n => fun v ↦ ∃ ts : Fin n → Tree,
        (∀ i, rs i (Eval.Val.quote (ts i))) ∧
          v = Eval.Val.quote (RoseTree.node l (List.ofFn ts))
      | .unit => fun v ↦ v = Eval.Val.unit
      | .pair => fun v ↦ ∃ x y, rs 0 x ∧ rs 1 y ∧ v = Eval.Val.pair x y
      | .nil A => fun v ↦ v = RoseTree.node Label.nil [A]
      | .cons => fun v ↦ ∃ x xs, rs 0 x ∧ rs 1 xs ∧ v = RoseTree.node Label.cons [x, xs]
      | .closure _ A b n => fun v ↦ ∃ en : Fin n → Tree,
        (∀ i, rs i (en i)) ∧ v = Eval.Val.clo (List.ofFn en) A b
      | .partialApp _ h n => fun v ↦ ConstantHead h ∧ ∃ args : Fin n → Tree,
        (∀ i, rs i (args i)) ∧ v = (List.ofFn args).foldl Eval.Val.app h
      | .thunk _ _ _ => fun _ ↦ False

/-- Mapping expressions into a tree constructor preserves the source list's port indices. -/
theorem tree_map {α : Type} {n : ℕ} (l : ℕ) (f : α → E n) (xs : List α) :
    tree l (xs.map f) = Expr.con (.tree l xs.length) (fun i ↦ f (xs.get i)) := by
  unfold tree con Expr.con
  apply Term.agent_congr (congrArg (fun k ↦ Sum.inl (Constructor.tree l k))
    (List.length_map (f := f)))
  intro i
  simp only [Fin.getElem_fin, List.get_eq_getElem, List.getElem_map, Fin.val_cast]

/-- A node's canonical value retains the source children's port indices. -/
theorem treeValue_node_get (l : ℕ) (ts : List Tree) :
    treeValue (RoseTree.node l ts) =
      Term.agent (.inl (.tree l ts.length)) (fun i ↦ treeValue (ts.get i)) := by
  rw [treeValue_node]
  apply Term.agent_congr (congrArg (fun k ↦ Sum.inl (Constructor.tree l k))
    (List.length_map (f := treeValue)))
  intro i
  simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]

/-- A literal evaluates to its canonical constructor value in every environment. -/
theorem evaluates_literal (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity) (t : Tree) :
    Evaluates dataArity (program P) (literal t) ρ (treeValue t) := by
  apply RoseTree.ind (P := fun t ↦
    Evaluates dataArity (program P) (literal t) ρ (treeValue t)) (fun l ts ih ↦ ?_) t
  change Evaluates _ _ (RoseTree.elim _ _) _ _
  rw [RoseTree.elim_node, tree_map, treeValue_node_get]
  apply evaluates_con
  intro i
  exact ih (ts[i.val]) (List.getElem_mem i.isLt)

/-- Canonical runtime trees represent their quotations in the evaluator. -/
theorem rep_treeValue (t : Tree) : Rep (treeValue t) (Eval.Val.quote t) := by
  apply RoseTree.ind (P := fun t ↦ Rep (treeValue t) (Eval.Val.quote t))
    (fun l ts ih ↦ ?_) t
  rw [treeValue_node_get]
  refine ⟨ts.get, fun i ↦ ih (ts.get i) (List.get_mem ..), ?_⟩
  rw [List.ofFn_get]

/-- A represented result of contextual expression evaluation. -/
def EvaluatesTo (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (e : E n) (v : Tree) : Prop :=
  ∃ w, Evaluates dataArity (program P) e ρ w ∧ Rep w v

/-- Literal expressions evaluate to the corresponding quoted evaluator value. -/
theorem evaluatesTo_literal (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity) (t : Tree) :
    EvaluatesTo P ρ (literal t) (Eval.Val.quote t) :=
  ⟨treeValue t, evaluates_literal P ρ t, rep_treeValue t⟩

private theorem exists_fields {α : Type} {n : ℕ} (R : Fin n → α → Prop)
    (h : ∀ i, ∃ a, R i a) : ∃ f : Fin n → α, ∀ i, R i (f i) := by
  apply Nat.rec (motive := fun n ↦ ∀ R : Fin n → α → Prop,
    (∀ i, ∃ a, R i a) → ∃ f : Fin n → α, ∀ i, R i (f i))
    (fun _ _ ↦ ⟨Fin.elim0, fun i ↦ i.elim0⟩) (fun n ih R h ↦ ?_) n R h
  obtain ⟨a, ha⟩ := h 0
  obtain ⟨f, hf⟩ := ih (fun i ↦ R i.succ) (fun i ↦ h i.succ)
  exact ⟨Fin.cases a f, Fin.cases ha hf⟩

/-- Finitely many represented evaluations can be assembled without a choice principle. -/
theorem evaluatesTo_fields (P : List Tree) {n k : ℕ} (ρ : Fin n → Value dataArity)
    (es : Fin k → E n) (vs : Fin k → Tree) (h : ∀ i, EvaluatesTo P ρ (es i) (vs i)) :
    ∃ ws : Fin k → Value dataArity,
      (∀ i, Evaluates dataArity (program P) (es i) ρ (ws i)) ∧ (∀ i, Rep (ws i) (vs i)) := by
  obtain ⟨ws, hw⟩ := exists_fields (fun i w ↦
    Evaluates dataArity (program P) (es i) ρ w ∧ Rep w (vs i)) h
  exact ⟨ws, fun i ↦ (hw i).1, fun i ↦ (hw i).2⟩

/-- An application spine has its head's label when empty, and the application label otherwise. -/
theorem spineValue_label (h : Tree) (args : List Tree) :
    (args.foldl Eval.Val.app h).label = if args.isEmpty then h.label else Label.app := by
  apply List.rec (motive := fun args ↦ ∀ h,
    (args.foldl Eval.Val.app h).label = if args.isEmpty then h.label else Label.app)
    (fun _ ↦ rfl) (fun a as ih h ↦ ?_) args h
  rw [List.foldl_cons, ih]
  cases as <;> rfl

/-- A constant's represented application spine cannot have a data-value label. -/
theorem ConstantHead.spine_ne {h : Tree} (hh : ConstantHead h) (args : List Tree) (l : ℕ)
    (hl : l ≠ Label.app ∧ l ≠ Label.fold ∧ l ≠ Label.para ∧ l ≠ Label.iter ∧
      l ≠ Label.foldr ∧ l ≠ Label.lcase ∧ l ≠ Label.prim) :
    (args.foldl Eval.Val.app h).label ≠ l := by
  rw [spineValue_label]
  split
  · rcases hh with hh | hh | hh | hh | hh | hh <;> omega
  · exact Ne.symm hl.1

/-- A runtime representation of a quoted tree is its canonical tree value. -/
theorem eq_treeValue_of_rep (v : Value dataArity) (t : Tree)
    (h : Rep v (Eval.Val.quote t)) : v = treeValue t := by
  apply PFunctor.FreeM.rec (motive := fun v ↦ ∀ t,
    Rep v (Eval.Val.quote t) → v = treeValue t)
    (fun x ↦ x.elim) (fun a vs ih t h ↦ ?_) v t h
  cases a with
  | inr n => exact False.elim h
  | inl a =>
    cases a with
    | tree l k =>
      obtain ⟨ts, ht, he⟩ := h
      have he' : t = RoseTree.node l (List.ofFn ts) := by
        have hh := congrArg RoseTree.children he
        simpa only [Eval.Val.quote, RoseTree.children_node, List.cons.injEq,
          and_true] using hh
      subst t
      rw [treeValue_node_get]
      apply Term.agent_congr
        (congrArg (fun n ↦ Sum.inl (Constructor.tree l n)) (List.length_ofFn (f := ts)).symm)
      intro i
      rw [List.get_ofFn]
      exact (ih i (ts i) (ht i)).trans
        (congrArg (fun j ↦ treeValue (ts j)) (Fin.ext rfl))
    | partialApp site head k =>
      obtain ⟨hh, args, _, he⟩ := h
      exact False.elim (hh.spine_ne (List.ofFn args) Label.quote (by decide)
        (by rw [← he]; rfl))
    | thunk => exact False.elim h
    | unit =>
      have hh := congrArg RoseTree.label h
      exact False.elim (by cases hh)
    | pair =>
      obtain ⟨x, y, _, _, he⟩ := h
      have hh := congrArg RoseTree.label he
      exact False.elim (by cases hh)
    | nil =>
      have hh := congrArg RoseTree.label h
      exact False.elim (by cases hh)
    | cons =>
      obtain ⟨x, xs, _, _, he⟩ := h
      have hh := congrArg RoseTree.label he
      exact False.elim (by cases hh)
    | closure =>
      obtain ⟨en, _, he⟩ := h
      have hh := congrArg RoseTree.label he
      exact False.elim (by cases hh)

end Geb.InteractionNet.Kernel

end
