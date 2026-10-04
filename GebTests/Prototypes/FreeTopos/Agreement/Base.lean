/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Metalogic
public import GebTests.Prototypes.FreeTopos.Agreement.Encode
public import GebTests.Prototypes.GoedelT.MirrorTyping

set_option doc.verso true in
/-!
# Optional trees, truth values and lists in the checker written in Geb

The values the prelude and {lit}`bootstrap/free-topos/base.geb` compute, in the Lean the
bootstrap compiler emits from the metalogic's checker ({lit}`GebMirror.Metalogic`): the kernel's
primitives at leaves and nodes, optional trees, truth values and lists, each stated as the
encoding of the Lean value it represents.

## Main definitions

* {lit}`natReflBEq` — the reflexivity of the equality test of natural numbers the simplifications
  use, from its lawfulness.

## Main statements

* {lit}`bindO_eq`, {lit}`mapO_eq` — the binding and mapping of optional trees.
* {lit}`nth_eq`, {lit}`take_eq`, {lit}`drop_eq`, {lit}`range_eq` — lists by position.
* {lit}`allT_eq`, {lit}`allSomeT_eq` — tests and traversals of lists.

## Tags

optional tree, truth value, list, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Base

open Geb Geb.Kernel GebTests.Prototypes.FreeTopos.Agreement.Encode
open scoped FinEnum

/-- The reflexivity of the equality test of natural numbers from its lawfulness, which the
simplifications of the mirrors use: where the imports reach the order's derivation of it, which
depends on {name}`Classical.choice`, instance search would otherwise select that. -/
instance (priority := high) natReflBEq : ReflBEq ℕ := Nat.instLawfulBEq.toReflBEq

-- the kernel's primitives at leaves and nodes, shared with the mirror of Gödel's T
export GebTests.Prototypes.GoedelT.MirrorTyping (label_leaf ofBool_label label_node children_node
  arity_node child_node)

attribute [simp] label_node arity_node child_node

/-- The comparison of two labels' equality. -/
@[simp] theorem eq_leaf (a b : ℕ) : Const.eq (leaf a) (leaf b) = ofBool (a == b) := rfl

/-- The comparison of two labels' order. -/
@[simp] theorem lt_leaf (a b : ℕ) : Const.lt (leaf a) (leaf b) = ofBool (decide (a < b)) := rfl

/-- The sum of two labels. -/
@[simp] theorem add_leaf (a b : ℕ) : Const.add (leaf a) (leaf b) = leaf (a + b) := rfl

/-- The truncated difference of two labels. -/
@[simp] theorem sub_leaf (a b : ℕ) : Const.sub (leaf a) (leaf b) = leaf (a - b) := rfl

/-- The product of two labels. -/
@[simp] theorem mul_leaf (a b : ℕ) : Const.mul (leaf a) (leaf b) = leaf (a * b) := rfl

/-- The comparison of two trees' equality. -/
@[simp] theorem equal_eq (a b : Tree) : Const.equal a b = ofBool (decide (a = b)) := rfl

/-- The node of a leaf's label. -/
@[simp] theorem node_leaf (l : ℕ) (cs : List Tree) : Const.node (leaf l) cs = RoseTree.node l cs :=
  rfl

/-- The leaf of a tree's label. -/
@[simp] theorem label_eq (t : Tree) : Const.label t = leaf t.label := rfl

/-- The children of a tree. -/
@[simp] theorem children_eq (t : Tree) : Const.children t = t.children := rfl

/-- The leaf of the number of a tree's children. -/
@[simp] theorem arity_eq (t : Tree) : Const.arity t = leaf t.children.length := by
  rw [← arity_node t.label t.children, RoseTree.node_label_children]

/-- The right fold of lists. -/
@[simp] theorem foldr_eq {α β : Type} (g : α → β → β) (z : β) (xs : List α) :
    Const.foldr g z xs = xs.foldr g z := rfl

/-- Case analysis of the empty list. -/
@[simp] theorem lcase_nil {α β : Type} (n : β) (c : α → List α → β) :
    Const.lcase ([] : List α) n c = n := rfl

/-- Case analysis of a construction. -/
@[simp] theorem lcase_cons {α β : Type} (x : α) (r : List α) (n : β) (c : α → List α → β) :
    Const.lcase (x :: r) n c = c x r := rfl

/-- Iteration as many times as a leaf's label. -/
@[simp] theorem iter_leaf {α : Type} (s : α → α) (z : α) (n : ℕ) :
    Const.iter s z (leaf n) = Nat.repeat s n z := rfl

/-- A list's length is zero exactly when it is empty. -/
@[simp] theorem length_beq_zero {α : Type} (xs : List α) : (xs.length == 0) = xs.isEmpty := by
  cases xs <;> rfl

/-- The encoding of optional trees is injective. -/
theorem encOpt_inj {a b : Option Tree} : encOpt a = encOpt b ↔ a = b := by
  refine ⟨fun h ↦ ?_, congrArg encOpt⟩
  cases a <;> cases b
  · rfl
  · exact absurd (congrArg RoseTree.label h) (by simp [encOpt, leaf])
  · exact absurd (congrArg RoseTree.label h) (by simp [encOpt, leaf])
  · have := congrArg RoseTree.children h
    simp only [encOpt, RoseTree.children_node, List.cons.injEq, and_true] at this
    rw [this]

/-- Leaves are injective. -/
theorem leaf_inj {a b : ℕ} : leaf a = leaf b ↔ a = b :=
  ⟨fun h ↦ congrArg RoseTree.label h, fun h ↦ h ▸ rfl⟩

/-- The truth value false is the leaf of label zero. -/
theorem ofBool_false : ofBool false = leaf 0 := rfl

/-- The truth value true is the leaf of label one. -/
theorem ofBool_true : ofBool true = leaf 1 := rfl

/-- A truth value has label zero exactly when it is false. -/
theorem ofBool_label_eq_zero (b : Bool) : ((ofBool b).label = 0) = (b = false) := by
  cases b <;> simp [ofBool]

/-- The label test of a truth value is the Boolean. -/
@[simp] theorem ofBool_bne (b : Bool) : ((ofBool b).label != 0) = b := by
  cases b <;> rfl

/-- Lists of leaves are equal exactly when their labels are. -/
@[simp] theorem map_leaf_inj {xs ys : List ℕ} : xs.map leaf = ys.map leaf ↔ xs = ys :=
  List.map_inj_right fun _ _ ↦ leaf_inj.mp

/-- The mirror's present optional tree. -/
theorem some_eq (t : Tree) : «Prelude.some» t = encOpt (some t) := rfl

/-- The mirror's absent optional tree. -/
theorem none_eq : «Prelude.none» = encOpt none := rfl

/-- The mirror's test of an optional tree's presence. -/
@[simp] theorem isSome_eq (o : Option Tree) :
    «Prelude.isSome» (encOpt o) = ofBool o.isSome := by
  cases o <;> rfl

/-- The mirror's tree of a present optional tree. -/
theorem get_eq (t : Tree) : «Prelude.get» (encOpt (some t)) = t := by
  simp [«Prelude.get», encOpt]

/-- The mirror's tree of an optional tree, or a default. -/
@[simp] theorem getD_eq (o : Option Tree) (d : Tree) :
    «Base.getD» (encOpt o) d = o.getD d := by
  cases o <;> simp [«Base.getD», get_eq]

/-- The mirror's image of an optional tree. -/
@[simp] theorem mapO_eq (f : Tree → Tree) (o : Option Tree) :
    «Base.mapO» f (encOpt o) = encOpt (o.map f) := by
  cases o <;> simp [«Base.mapO», some_eq, none_eq, get_eq]

/-- The mirror's binding of an optional tree. -/
@[simp] theorem bindO_eq (o : Option Tree) (f : Tree → Tree) :
    «Base.bindO» (encOpt o) f = o.elim (encOpt none) f := by
  cases o <;> simp [«Base.bindO», none_eq, get_eq]

/-- The mirror's conjunction of truth values. -/
@[simp] theorem and_eq (a b : Bool) :
    «Prelude.and» (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- The mirror's disjunction of truth values. -/
@[simp] theorem or_eq (a b : Bool) :
    «Prelude.or» (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-- The mirror's negation of a truth value. -/
@[simp] theorem not_eq (a : Bool) : «Base.not» (ofBool a) = ofBool (!a) := by
  cases a <;> rfl

/-- The mirror's length of a list. -/
@[simp] theorem length_eq (xs : List Tree) : «Prelude.length» xs = leaf xs.length :=
  xs.rec rfl fun _ _ ih ↦ by
    simp only [«Prelude.length», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The mirror's appending of lists. -/
@[simp] theorem append_eq (xs ys : List Tree) : «Prelude.append» xs ys = xs ++ ys :=
  xs.rec rfl fun _ _ ih ↦ by
    simp only [«Prelude.append», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The mirror's list of one tree. -/
@[simp] theorem single_eq (x : Tree) : «Prelude.single» x = [x] := rfl

/-- The mirror's reversal of a list. -/
@[simp] theorem reverse_eq (xs : List Tree) : «Prelude.reverse» xs = xs.reverse := by
  have h : ∀ acc : List Tree, xs.foldr (fun x (k : List Tree → List Tree) acc ↦ k (x :: acc))
      (fun acc ↦ acc) acc = xs.reverse ++ acc :=
    xs.rec (fun _ ↦ rfl) fun x r ih acc ↦ by simp [ih]
  simp only [«Prelude.reverse», foldr_eq]
  exact (h []).trans (List.append_nil _)

/-- The mirror's list of copies of a tree. -/
@[simp] theorem replicate_eq (n : ℕ) (x : Tree) :
    «Prelude.replicate» (leaf n) x = List.replicate n x := by
  simp only [«Prelude.replicate», iter_leaf]
  exact Nat.rec rfl (fun n ih ↦ by rw [Nat.repeat, ih]; rfl) n

/-- The mirror's element of a list at a position, the leaf of label zero when out of range. -/
@[simp] theorem at_eq (xs : List Tree) (i : ℕ) :
    «Prelude.at» xs (leaf i) = xs.getD i (leaf 0) :=
  child_node 0 i xs

/-- The mirror's element of a list at a position. -/
@[simp] theorem nth_eq (xs : List Tree) (i : ℕ) :
    «Prelude.nth» xs (leaf i) = encOpt xs[i]? := by
  simp only [«Prelude.nth», length_eq, lt_leaf, ofBool_label, decide_eq_true_eq]
  split
  · rename_i h
    simp [some_eq, h]
  · rename_i h
    rw [none_eq, List.getElem?_eq_none (Nat.le_of_not_lt h)]

/-- The mirror's test of a list's emptiness. -/
@[simp] theorem isEmpty_eq (xs : List Tree) :
    «Base.isEmpty» xs = ofBool xs.isEmpty := by
  cases xs <;> rfl

/-- The mirror's comparison of two lists' equality. -/
@[simp] theorem equalTs_eq (xs ys : List Tree) :
    «Base.equalTs» xs ys = ofBool (decide (xs = ys)) := by
  simp only [«Base.equalTs», node_leaf, equal_eq]
  congr 1
  exact decide_eq_decide.mpr
    ⟨fun h ↦ (RoseTree.node_eq_iff.mp h).2.trans (RoseTree.children_node 0 ys), fun h ↦ h ▸ rfl⟩

/-- The mirror's list without its head. -/
@[simp] theorem tail_eq (xs : List Tree) : «Prelude.tail» xs = xs.tail := by
  cases xs <;> rfl

/-- The mirror's list without its first elements. -/
@[simp] theorem drop_eq (n : ℕ) (xs : List Tree) :
    «Prelude.drop» (leaf n) xs = xs.drop n := by
  simp only [«Prelude.drop», iter_leaf]
  exact Nat.rec rfl (fun n ih ↦ by rw [Nat.repeat, ih, tail_eq, List.tail_drop]) n

/-- The mirror's image of a list. -/
@[simp] theorem mapT_eq (f : Tree → Tree) (xs : List Tree) :
    «Base.mapT» f xs = xs.map f :=
  xs.rec rfl fun _ _ ih ↦ by
    simp only [«Base.mapT», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The mirror's test that every element of a list passes a test. -/
theorem allT_eq (f : Tree → Tree) (p : Tree → Bool) :
    ∀ xs : List Tree, (∀ x ∈ xs, f x = ofBool (p x)) →
      «Base.allT» f xs = ofBool (xs.all p) :=
  List.rec (fun _ ↦ rfl) fun x r ih h ↦ by
    have ih' := ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)
    simp only [«Base.allT», foldr_eq, List.foldr_cons] at ih' ⊢
    rw [ih', h x List.mem_cons_self, and_eq, List.all_cons]

/-- The mirror's test that every element of an encoded list passes a test. -/
theorem allT_map {α : Type} (f : Tree → Tree) (e : α → Tree) (p : α → Bool) :
    ∀ xs : List α, (∀ x ∈ xs, f (e x) = ofBool (p x)) →
      «Base.allT» f (xs.map e) = ofBool (xs.all p) :=
  List.rec (fun _ ↦ rfl) fun x r ih h ↦ by
    have ih' := ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)
    simp only [«Base.allT», foldr_eq, List.map_cons, List.foldr_cons] at ih' ⊢
    rw [ih', h x List.mem_cons_self, and_eq, List.all_cons]

/-- The mirror's conjunction of a list of truth values. -/
theorem allT_ofBool {α : Type} (q : α → Bool) (xs : List α) :
    «Base.allT» (fun t ↦ t) (xs.map fun x ↦ ofBool (q x)) = ofBool (xs.all q) :=
  xs.rec rfl fun x r ih ↦ by
    simp only [«Base.allT», foldr_eq, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, and_eq, List.all_cons]

/-- The label test of the mirror's conjunction. -/
@[simp] theorem and_label (a b : Tree) :
    ((«Prelude.and» a b).label != 0) = ((a.label != 0) && (b.label != 0)) := by
  simp only [«Prelude.and»]
  by_cases h : a.label = 0 <;> simp [h, leaf]

/-- The label test of the mirror's disjunction. -/
@[simp] theorem or_label (a b : Tree) :
    ((«Prelude.or» a b).label != 0) = ((a.label != 0) || (b.label != 0)) := by
  simp only [«Prelude.or»]
  by_cases h : a.label = 0 <;> simp [h, leaf]

/-- The label test of the mirror's negation. -/
@[simp] theorem not_label (a : Tree) :
    ((«Base.not» a).label != 0) = !(a.label != 0) := by
  simp only [«Base.not»]
  by_cases h : a.label = 0 <;> simp [h, leaf]

/-- The label test of the mirror's test that every element of a list passes a test. -/
@[simp] theorem allT_label (f : Tree → Tree) (xs : List Tree) :
    ((«Base.allT» f xs).label != 0) = xs.all fun x ↦ (f x).label != 0 :=
  xs.rec rfl fun x r ih ↦ by
    simp only [«Base.allT», foldr_eq, List.foldr_cons, List.all_cons] at ih ⊢
    rw [and_label, ih]

/-- The label test of a comparison of trees. -/
theorem equal_label (a b : Tree) : ((Const.equal a b).label != 0) = decide (a = b) := by
  simp [Const.equal, ofBool_bne]

/-- The label test of a comparison of labels. -/
@[simp] theorem eq_label (a b : Tree) : ((Const.eq a b).label != 0) = (a.label == b.label) := by
  simp [Const.eq, ofBool_bne]

/-- The label test of an order of labels. -/
@[simp] theorem lt_label (a b : Tree) :
    ((Const.lt a b).label != 0) = decide (a.label < b.label) := by
  simp [Const.lt, ofBool_bne]

/-- The mirror's test that some element of a list passes a test. -/
theorem anyT_eq (f : Tree → Tree) (p : Tree → Bool) :
    ∀ xs : List Tree, (∀ x ∈ xs, f x = ofBool (p x)) →
      «Base.anyT» f xs = ofBool (xs.any p) :=
  List.rec (fun _ ↦ rfl) fun x r ih h ↦ by
    have ih' := ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)
    simp only [«Base.anyT», foldr_eq, List.foldr_cons] at ih' ⊢
    rw [ih', h x List.mem_cons_self, or_eq, List.any_cons]

/-- The traversal of a list by a function to optional trees: the list of the trees where each
is present. -/
theorem mapM_option {α : Type} (f : α → Option Tree) :
    ∀ xs : List α, xs.mapM f = if xs.all (fun x ↦ (f x).isSome) = true then
      some (xs.map fun x ↦ (f x).getD (leaf 0)) else none :=
  List.rec rfl fun x r ih ↦ by
    rw [List.mapM_cons, ih, List.all_cons, List.map_cons]
    cases hf : f x <;> cases hr : r.all (fun x ↦ (f x).isSome) <;> simp

/-- The mirror's tree of an optional tree, the leaf of label zero when absent. -/
@[simp] theorem get_encOpt (o : Option Tree) :
    «Prelude.get» (encOpt o) = o.getD (leaf 0) := by
  cases o
  · exact child_node 0 0 []
  · exact get_eq _

/-- The label test of an optional tree's presence. -/
theorem encOpt_label (o : Option Tree) : ((encOpt o).label == 1) = o.isSome := by
  cases o <;> rfl

/-- The mirror's list of the trees of a list of optional trees where each is present. -/
theorem allSomeT_eq {α : Type} (f : α → Option Tree) (xs : List α) :
    «Base.allSomeT» (xs.map fun x ↦ encOpt (f x)) =
      encOpt ((xs.mapM f).map (RoseTree.node 0)) := by
  rw [mapM_option, «Base.allSomeT»,
    allT_eq «Prelude.isSome» (fun t ↦ t.label == 1) _ fun _ _ ↦ rfl]
  simp only [mapT_eq, List.map_map, Function.comp_def, get_encOpt, List.all_map, encOpt_label]
  cases xs.all (fun x ↦ (f x).isSome) <;> rfl

/-- The mirror's first elements of a list, counted from its end. -/
theorem take_foldr (L n : ℕ) : ∀ ys : List Tree, ys.length ≤ L →
    ys.foldr (fun (y : Tree) (s : Tree × List Tree) ↦ (Const.add s.1 (leaf 1),
      if (Const.lt (Const.sub (Const.sub (leaf L) s.1) (leaf 1)) (leaf n)).label ≠ 0 then
        y :: s.2 else s.2)) (leaf 0, []) = (leaf ys.length, ys.take (n - (L - ys.length))) :=
  List.rec (fun _ ↦ by simp) fun y ys ih h ↦ by
    rw [List.foldr_cons, ih (Nat.le_of_succ_le h)]
    simp only [add_leaf, sub_leaf, lt_leaf, ofBool_label, decide_eq_true_eq, List.length_cons]
    split
    · rename_i hl
      rw [show n - (L - (ys.length + 1)) = (n - (L - ys.length)) + 1 by
        simp only [List.length_cons] at h; omega, List.take_succ_cons]
    · rename_i hl
      rw [show n - (L - (ys.length + 1)) = 0 by simp only [List.length_cons] at h; omega,
        show n - (L - ys.length) = 0 by simp only [List.length_cons] at h; omega]
      rfl

/-- The mirror's first elements of a list. -/
@[simp] theorem take_eq (n : ℕ) (xs : List Tree) :
    «Base.take» (leaf n) xs = xs.take n := by
  simp only [«Base.take», length_eq, foldr_eq]
  rw [take_foldr xs.length n xs le_rfl, Nat.sub_self, Nat.sub_zero]

/-- The mirror's labels below a number, in order. -/
@[simp] theorem range_eq (n : ℕ) :
    «Base.range» (leaf n) = (List.range n).map leaf := by
  have h : ∀ n : ℕ, Nat.repeat (fun (s : Tree × List Tree) ↦ (Const.add s.1 (leaf 1),
      «Prelude.append» s.2 («Prelude.single» s.1))) n (leaf 0, []) =
      (leaf n, (List.range n).map leaf) :=
    Nat.rec rfl fun n ih ↦ by
      rw [Nat.repeat, ih]
      simp [List.range_succ]
  simp only [«Base.range», iter_leaf]
  rw [h]

/-- A list of leaves equals the leaves of a list's images exactly when the labels equal the
images. -/
@[simp] theorem map_leaf_eq_map {α : Type} (xs : List ℕ) (ys : List α) (f : α → ℕ) :
    (xs.map leaf = ys.map fun y ↦ leaf (f y)) ↔ xs = ys.map f := by
  rw [← map_leaf_inj, List.map_map]
  rfl

/-- The leaves of a list's images equal a list of leaves exactly when the images equal the
labels. -/
@[simp] theorem map_eq_map_leaf {α : Type} (xs : List ℕ) (ys : List α) (f : α → ℕ) :
    (ys.map (fun y ↦ leaf (f y)) = xs.map leaf) ↔ ys.map f = xs := by
  rw [eq_comm, map_leaf_eq_map, eq_comm]

/-- The right fold that keeps the first element of an encoded list passing a test finds it. -/
theorem foldr_find {α : Type} (e : α → Tree) (p : Tree → Bool) (xs : List α) :
    (xs.map e).foldr (fun x r ↦ if p x = true then encOpt (some x) else r)
        «Prelude.none» =
      encOpt ((xs.find? fun y ↦ p (e y)).map e) :=
  xs.rec rfl fun y ys ih ↦ by
    rw [List.map_cons, List.foldr_cons, ih, List.find?_cons]
    cases p (e y) <;> rfl

/-- The label test of a tree, as a Boolean. -/
theorem label_ne_zero (t : Tree) : (t.label ≠ 0) = ((t.label != 0) = true) := by
  simp

/-- Rewrites the mirror's primitives, optional trees, truth values and lists at encoded inputs
into the Lean values they encode, with further lemmas. -/
macro (name := mirrorSimp) "mirror_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [label_leaf, eq_leaf, lt_leaf, add_leaf, sub_leaf, mul_leaf, equal_eq, label_node,
    node_leaf, children_node, arity_node, label_eq, children_eq, arity_eq, child_node, foldr_eq,
    lcase_nil, lcase_cons, iter_leaf, isSome_eq, get_eq, getD_eq, mapO_eq, bindO_eq, and_eq, or_eq,
    not_eq, length_eq, append_eq, single_eq, reverse_eq, replicate_eq, at_eq, nth_eq, isEmpty_eq,
    equalTs_eq, tail_eq, drop_eq, mapT_eq, take_eq, range_eq, get_encOpt, and_label, or_label,
    not_label, allT_label, equal_label, eq_label, lt_label, ofBool_bne, map_leaf_inj,
    map_leaf_eq_map, map_eq_map_leaf, length_beq_zero, label_ne_zero, List.map_map,
    Function.comp_def, List.length_map, List.getElem?_map, Option.map_map, Array.getElem?_toList,
    List.all_map, List.isEmpty_map, Option.isSome_some, Option.isSome_none, Option.getD_some,
    Option.getD_none, Option.map_some, Option.map_none, Option.elim_some, Option.elim_none,
    Option.bind_some, Option.bind_none, Bool.true_and, Bool.and_true, Bool.false_and,
    Bool.and_false, Bool.not_true, Bool.not_false, ↓reduceIte, beq_self_eq_true, Nat.reduceBEq,
    RoseTree.label_node, RoseTree.children_node, List.getD_cons_zero, List.getD_cons_succ,
    Bool.false_eq_true, List.tail_cons, List.map_cons, List.map_nil, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Bool.or_false, Bool.false_or,
    Bool.or_true, Bool.true_or, zero_add, Nat.reduceAdd, $ls,*] $(loc)?)

end GebTests.Prototypes.FreeTopos.Agreement.Base

end
