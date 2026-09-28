/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.GoedelT.MirrorTyping
public import Geb.Prototypes.Kernel.Subst

set_option doc.verso true in
/-!
# The traversal of kernel terms written in Geb

The traversal of de Bruijn terms written in Geb, which replaces each variable by a function of
the number of binders around it and of its index, and the weakening and substitution defined
from it, are proved equal in their Lean mirror to the kernel's {name}`Geb.Kernel.trav`,
{name}`Geb.Kernel.wk` and {name}`Geb.Kernel.subst`: {lit}`trav_eq`, {lit}`wk_eq` and
{lit}`subst_eq`. The mirror's fold carries each node with the function of the number of binders;
at a variable it applies the replacement, at an abstraction it traverses the body under one more
binder, and at a node whose children are all terms it traverses each child.

## Main statements

* {lit}`trav_eq` — the mirror's traversal is the kernel's, when their replacements agree.
* {lit}`wk_eq`, {lit}`subst_eq` — the mirror's weakening and substitution are the kernel's.

## Tags

de Bruijn index, weakening, substitution, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.GoedelT.MirrorTerms

open Geb Geb.Kernel GebTests.Prototypes.GoedelT.MirrorTyping
open scoped FinEnum

/-- The trees of a list of trees with their functions. -/
theorem trTrees_eq (rs : List (Tree × (Tree → Tree))) :
    GebMirror.GoedelT.trTrees rs = rs.map (·.1) :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [GebMirror.GoedelT.trTrees, Const.foldr, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The functions of a list of trees with their functions, applied to a tree. -/
theorem trAll_eq (rs : List (Tree × (Tree → Tree))) (k : Tree) :
    GebMirror.GoedelT.trAll rs k = rs.map (·.2 k) :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [GebMirror.GoedelT.trAll, Const.foldr, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The step of the mirror's traversal at a node: the node rebuilt, and its traversal as a
function of the number of binders around it. -/
def travStep (v : Tree → Tree → Tree) (l : Tree) (rs : List (Tree × (Tree → Tree))) :
    Tree × (Tree → Tree) :=
  (Const.node l (GebMirror.GoedelT.trTrees rs), fun k ↦
    if (GebMirror.GoedelT.and (Const.eq l (leaf 8))
        (Const.eq (GebMirror.GoedelT.length (GebMirror.GoedelT.trTrees rs)) (leaf 1))).label ≠ 0
    then v k (Const.label (GebMirror.GoedelT.at (GebMirror.GoedelT.trTrees rs) (leaf 0)))
    else if (GebMirror.GoedelT.and (Const.eq l (leaf 9))
        (Const.eq (GebMirror.GoedelT.length (GebMirror.GoedelT.trTrees rs)) (leaf 2))).label ≠ 0
    then GebMirror.GoedelT.node2 (leaf 9)
      (GebMirror.GoedelT.at (GebMirror.GoedelT.trTrees rs) (leaf 0))
      (GebMirror.GoedelT.at (GebMirror.GoedelT.trAll rs (Const.add k (leaf 1))) (leaf 1))
    else if (GebMirror.GoedelT.termNode l).label ≠ 0 then
      Const.node l (GebMirror.GoedelT.trAll rs k)
    else Const.node l (GebMirror.GoedelT.trTrees rs))

/-- The mirror's traversal is the fold of its step. -/
theorem trav_def (v : Tree → Tree → Tree) (t k : Tree) :
    GebMirror.GoedelT.trav v t k = (Const.fold (travStep v) t).2 k := rfl

/-- The mirror's disjunction of truth values. -/
theorem or_ofBool (a b : Bool) :
    GebMirror.GoedelT.or (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-- The mirror's test of a label whose children are all terms. -/
theorem termNode_label (l : ℕ) :
    (GebMirror.GoedelT.termNode (leaf l)).label ≠ 0 ↔ l ∈ [10, 11, 12, 13, 14, 16, 20] := by
  simp only [GebMirror.GoedelT.termNode, eq_leaf_ofBool, or_ofBool, ofBool_label, Bool.or_eq_true,
    beq_iff_eq, List.mem_cons, List.not_mem_nil, or_false]

/-- The traversal at a variable. -/
theorem trav_var (v : ℕ → ℕ → Tree) (k : ℕ) (n : Tree) :
    trav v (RoseTree.node Label.var [n]) k = v k n.label := by
  simp only [trav, RoseTree.para_node, List.map_singleton]

/-- The traversal at an abstraction. -/
theorem trav_lam (v : ℕ → ℕ → Tree) (k : ℕ) (A b : Tree) :
    trav v (RoseTree.node Label.lam [A, b]) k = RoseTree.node Label.lam [A, trav v b (k + 1)] := by
  simp only [trav, RoseTree.para_node, List.map_cons, List.map_nil]

/-- The traversal at a node whose children are kept. -/
theorem trav_other (v : ℕ → ℕ → Tree) (k l : ℕ) (cs : List Tree)
    (h8 : ¬(l = 8 ∧ cs.length = 1)) (h9 : ¬(l = 9 ∧ cs.length = 2))
    (ht : l ∉ [10, 11, 12, 13, 14, 16, 20]) :
    trav v (RoseTree.node l cs) k = RoseTree.node l cs := by
  simp only [trav, RoseTree.para_node]
  split
  case h_1 _ _ heq => exact absurd ⟨rfl, by simpa using congrArg List.length heq⟩ h8
  case h_2 _ _ _ _ heq => exact absurd ⟨rfl, by simpa using congrArg List.length heq⟩ h9
  case h_10 => simp only [List.map_map, Function.comp_def, List.map_id']
  all_goals simp at ht

/-- The mirror's traversal's fold gives each tree with its traversal, at every number of
binders, when the replacement of variables agrees with the kernel's. -/
theorem fold_travStep (v' : Tree → Tree → Tree) (v : ℕ → ℕ → Tree)
    (hv : ∀ k i, v' (leaf k) (leaf i) = v k i) :
    ∀ t : Tree, (Const.fold (travStep v') t).1 = t ∧
      ∀ k : ℕ, (Const.fold (travStep v') t).2 (leaf k) = trav v t k :=
  RoseTree.ind fun l cs ih ↦ by
    rw [fold_node]
    have htr : GebMirror.GoedelT.trTrees (cs.map (Const.fold (travStep v'))) = cs := by
      rw [trTrees_eq, List.map_map]
      exact (List.map_congr_left fun c hc ↦ (ih c hc).1).trans (List.map_id cs)
    refine ⟨by simp only [travStep, htr]; rfl, fun k ↦ ?_⟩
    simp only [travStep, htr, length_eq, eq_leaf_ofBool, and_ofBool, ofBool_label,
      Bool.and_eq_true, beq_iff_eq]
    split_ifs with h8 h9 hterm
    · obtain ⟨rfl, hlen⟩ := h8
      obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hlen
      rw [at_eq, trav_var]
      exact hv k c.label
    · obtain ⟨rfl, hlen⟩ := h9
      obtain ⟨A, b, rfl⟩ := List.length_eq_two.mp hlen
      rw [trAll_eq, at_eq, at_eq, trav_lam, node2_mirror, node2_eq]
      simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
      rw [show Const.add (leaf k) (leaf 1) = leaf (k + 1) from rfl,
        (ih b (by simp)).2 (k + 1)]
    · rw [termNode_label] at hterm
      rw [trAll_eq, List.map_map, trav_node_term v k hterm]
      exact congrArg (RoseTree.node l) (List.map_congr_left fun c hc ↦ (ih c hc).2 k)
    · rw [termNode_label] at hterm
      exact (trav_other v k l cs h8 h9 hterm).symm

/-- The mirror's traversal agrees with the kernel's, when their replacements of variables do. -/
theorem trav_eq (v' : Tree → Tree → Tree) (v : ℕ → ℕ → Tree)
    (hv : ∀ k i, v' (leaf k) (leaf i) = v k i) (t : Tree) (k : ℕ) :
    GebMirror.GoedelT.trav v' t (leaf k) = trav v t k :=
  (fold_travStep v' v hv t).2 k

/-- The mirror's variable. -/
theorem var_eq (i : ℕ) : GebMirror.GoedelT.var (leaf i) = Tm.var i := rfl

/-- The mirror's replacement of a variable in weakening. -/
theorem wkVar_eq (n k i : ℕ) :
    GebMirror.GoedelT.wkVar (leaf n) (leaf k) (leaf i) = wkVar n k i := by
  simp only [GebMirror.GoedelT.wkVar, Kernel.wkVar, lt_leaf]
  split_ifs <;> rfl

/-- The mirror's weakening. -/
theorem wk_eq (n : ℕ) (t : Tree) : GebMirror.GoedelT.wk (leaf n) t = wk n t :=
  trav_eq _ _ (wkVar_eq n) t 0

/-- The mirror's replacement of a variable in substitution. -/
theorem substVar_eq (u : Tree) (k i : ℕ) :
    GebMirror.GoedelT.substVar u (leaf k) (leaf i) = substVar u k i := by
  simp only [GebMirror.GoedelT.substVar, Kernel.substVar, lt_leaf, eq_leaf, wk_eq]
  split_ifs <;> rfl

/-- The mirror's substitution for the innermost variable. -/
theorem subst_eq (u t : Tree) : GebMirror.GoedelT.subst u t = subst u t :=
  trav_eq _ _ (substVar_eq u) t 0

end GebTests.Prototypes.GoedelT.MirrorTerms

end
