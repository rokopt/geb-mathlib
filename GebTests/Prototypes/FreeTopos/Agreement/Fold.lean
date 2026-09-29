/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Basic

set_option doc.verso true in
/-!
# Paramorphisms as folds

The metalogic's checker written in Geb computes a paramorphism, whose step reads each child's
tree as well as its result, as the kernel's fold of trees whose step pairs the node's tree,
rebuilt from its children's, with the result ({lit}`PairStep`). This module relates such a fold
to Lean's paramorphism {name}`Geb.RoseTree.para`: over the same tree, and over the encoding of a
rose tree of other labels as a tree of numbers, each node the node of its label's position over
the tree of the label's data and the children ({lit}`encWith`). Each relation holds when the
steps are related node by node, the results at the children related.

## Main definitions

* {lit}`PairStep` — a step of a fold that pairs each node's tree with a result.
* {lit}`encWith` — a rose tree of labels as a tree of numbers.

## Main statements

* {lit}`fold_pair_fst` — the fold rebuilds the tree.
* {lit}`fold_pair_snd` — the fold's result is related to a paramorphism of the tree.
* {lit}`fold_pair_enc` — the fold's result at an encoded tree is related to a paramorphism
  of the tree it encodes.
* {lit}`elim_eq_para` — a fold is a paramorphism.
* {lit}`fold_rel`, {lit}`para_rel` — a fold, and the kernel's fold whose step sees the node, is
  related to a fold, and a paramorphism, of the same tree.
* {lit}`encWith_inj` — the encoding is injective where a label's position and data determine it.

## Tags

paramorphism, fold, rose tree, encoding, agreement
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Agreement.Fold

open Geb Geb.Kernel

/-- The fold at a node is its step at the node's label and its children's results. -/
theorem fold_node {α : Type} (f : Tree → List α → α) (a : ℕ) (cs : List Tree) :
    Const.fold f (RoseTree.node a cs) = f (leaf a) (cs.map (Const.fold f)) :=
  RoseTree.elim_node _ a cs

/-- A step of a fold pairs each node's tree with a result when its first component is the node
of the label over the children's trees. -/
def PairStep {V : Type} (st : Tree → List (Tree × V) → Tree × V) : Prop :=
  ∀ l rs, (st l rs).1 = Const.node l (rs.map Prod.fst)

/-- A fold pairing each node's tree with a result rebuilds the tree. -/
theorem fold_pair_fst {V : Type} {st : Tree → List (Tree × V) → Tree × V} (hst : PairStep st)
    (t : Tree) : (Const.fold st t).1 = t := by
  refine RoseTree.ind (P := fun t ↦ (Const.fold st t).1 = t) (fun a cs ih ↦ ?_) t
  rw [fold_node, hst]
  simp only [Const.node, leaf, RoseTree.label_node, List.map_map]
  congr 1
  exact (List.map_congr_left fun c hc ↦ ih c hc).trans (List.map_id _)

/-- A fold pairing each node's tree with a result gives, at a list of trees, each tree with its
result. -/
theorem map_fold_pair {V : Type} {st : Tree → List (Tree × V) → Tree × V} (hst : PairStep st)
    (cs : List Tree) : cs.map (Const.fold st) = cs.map fun c ↦ (c, (Const.fold st c).2) :=
  List.map_congr_left fun c _ ↦ Prod.ext (fold_pair_fst hst c) rfl

/-- A fold pairing each node's tree with a result is related to a paramorphism of the same tree
when their steps are related at every node whose children's results are related. -/
theorem fold_pair_snd {V W : Type} (R : V → W → Prop) {st : Tree → List (Tree × V) → Tree × V}
    (hst : PairStep st) (g : ℕ → List (Tree × W) → W)
    (h : ∀ (l : ℕ) (xs : List (Tree × V × W)), (∀ x ∈ xs, R x.2.1 x.2.2) →
      R (st (leaf l) (xs.map fun x ↦ (x.1, x.2.1))).2 (g l (xs.map fun x ↦ (x.1, x.2.2))))
    (t : Tree) : R (Const.fold st t).2 (RoseTree.para g t) := by
  refine RoseTree.ind (P := fun t ↦ R (Const.fold st t).2 (RoseTree.para g t))
    (fun a cs ih ↦ ?_) t
  have := h a (cs.map fun c ↦ (c, (Const.fold st c).2, RoseTree.para g c)) (by simpa using ih)
  rw [fold_node, RoseTree.para_node, map_fold_pair hst]
  simpa only [List.map_map, Function.comp_def] using this

/-- A fold is the paramorphism whose step sees the children's results alone. -/
theorem elim_eq_para {α β : Type} (f : α → List β → β) (t : RoseTree α) :
    RoseTree.elim f t = RoseTree.para (fun a rs ↦ f a (rs.map Prod.snd)) t :=
  RoseTree.ind
    (P := fun t ↦ RoseTree.elim f t = RoseTree.para (fun a rs ↦ f a (rs.map Prod.snd)) t)
    (fun a cs ih ↦ by
      rw [RoseTree.elim_node, RoseTree.para_node, List.map_map]
      exact congrArg (f a) (List.map_congr_left ih)) t

/-- A rose tree of labels as a tree of numbers: each node the node of its label's position over
the tree of the label's data and the children. -/
def encWith {L : Type} (tag : L → ℕ) (dat : L → Tree) : RoseTree L → Tree :=
  RoseTree.elim fun l cs ↦ RoseTree.node (tag l) (dat l :: cs)

/-- The encoding of a node is the node of its label's position over the label's data and the
children's encodings. -/
@[simp] theorem encWith_node {L : Type} (tag : L → ℕ) (dat : L → Tree) (l : L)
    (cs : List (RoseTree L)) :
    encWith tag dat (RoseTree.node l cs) =
      RoseTree.node (tag l) (dat l :: cs.map (encWith tag dat)) :=
  RoseTree.elim_node _ l cs

/-- Nodes are equal exactly when their labels and their children are. -/
theorem node_inj {L : Type} {a b : L} {cs ds : List (RoseTree L)} :
    RoseTree.node a cs = RoseTree.node b ds ↔ a = b ∧ cs = ds := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1 ▸ h.2 ▸ rfl⟩
  · simpa using congrArg RoseTree.label h
  · simpa using congrArg RoseTree.children h

/-- A map of lists is injective at a list whose elements it separates from every element. -/
theorem map_inj_of_mem {α β : Type} (f : α → β) :
    ∀ cs : List α, (∀ c ∈ cs, ∀ b, f c = f b → c = b) → ∀ ds, cs.map f = ds.map f → cs = ds :=
  List.rec (fun _ ds h ↦ (List.map_eq_nil_iff.mp h.symm).symm) fun c cs ih hc ds h ↦ by
    rcases ds with _ | ⟨d, ds⟩
    · exact absurd h (List.cons_ne_nil _ _)
    · simp only [List.map_cons, List.cons.injEq] at h
      rw [hc c List.mem_cons_self d h.1,
        ih (fun c' hc' ↦ hc c' (List.mem_cons_of_mem c hc')) ds h.2]

/-- The encoding of rose trees of labels is injective where a label's position and data
determine it. -/
theorem encWith_inj {L : Type} (tag : L → ℕ) (dat : L → Tree)
    (h : ∀ l l', tag l = tag l' → dat l = dat l' → l = l') :
    Function.Injective (encWith tag dat) := by
  intro s
  refine RoseTree.ind (P := fun s ↦ ∀ s', encWith tag dat s = encWith tag dat s' → s = s')
    (fun l cs ih s' hs ↦ ?_) s
  obtain ⟨l', cs', rfl⟩ : ∃ l' cs', s' = RoseTree.node l' cs' :=
    ⟨s'.label, s'.children, (RoseTree.node_label_children s').symm⟩
  rw [encWith_node, encWith_node, node_inj, List.cons.injEq] at hs
  rw [h l l' hs.1 hs.2.1, map_inj_of_mem _ cs ih cs' hs.2.2]

/-- A fold pairing each node's tree with a result, over an encoded tree, is related to a
paramorphism of the tree it encodes when their steps are related at every node whose children's
results are related, whatever the result at the tree of the label's data. -/
theorem fold_pair_enc {L V W : Type} (tag : L → ℕ) (dat : L → Tree) (R : V → W → Prop)
    {st : Tree → List (Tree × V) → Tree × V} (hst : PairStep st)
    (g : L → List (RoseTree L × W) → W)
    (h : ∀ (l : L) (v : V) (xs : List (RoseTree L × V × W)), (∀ x ∈ xs, R x.2.1 x.2.2) →
      R (st (leaf (tag l)) ((dat l, v) :: xs.map fun x ↦ (encWith tag dat x.1, x.2.1))).2
        (g l (xs.map fun x ↦ (x.1, x.2.2))))
    (s : RoseTree L) :
    R (Const.fold st (encWith tag dat s)).2 (RoseTree.para g s) := by
  refine RoseTree.ind
    (P := fun s ↦ R (Const.fold st (encWith tag dat s)).2 (RoseTree.para g s))
    (fun a cs ih ↦ ?_) s
  have := h a (Const.fold st (dat a)).2
    (cs.map fun c ↦ (c, (Const.fold st (encWith tag dat c)).2, RoseTree.para g c))
    (by simpa using ih)
  have e : Const.fold st (dat a) = (dat a, (Const.fold st (dat a)).2) :=
    Prod.ext (fold_pair_fst hst _) rfl
  rw [encWith_node, fold_node, RoseTree.para_node, List.map_cons, map_fold_pair hst, e]
  simpa only [List.map_map, Function.comp_def] using this

/-- A fold is related to a fold of the same tree when their steps are related at every node whose
children's results are related. -/
theorem fold_rel {V W : Type} (R : V → W → Prop) (f : Tree → List V → V) (g : ℕ → List W → W)
    (h : ∀ (l : ℕ) (xs : List (V × W)), (∀ x ∈ xs, R x.1 x.2) →
      R (f (leaf l) (xs.map Prod.fst)) (g l (xs.map Prod.snd)))
    (t : Tree) : R (Const.fold f t) (RoseTree.elim g t) := by
  refine RoseTree.ind (P := fun t ↦ R (Const.fold f t) (RoseTree.elim g t)) (fun a cs ih ↦ ?_) t
  have := h a (cs.map fun c ↦ (Const.fold f c, RoseTree.elim g c)) (by simpa using ih)
  rw [fold_node, RoseTree.elim_node]
  simpa only [List.map_map, Function.comp_def] using this

/-- The kernel's fold whose step sees the node is related to a paramorphism of the same tree when
their steps are related at every node whose children's results are related. -/
theorem para_rel {V W : Type} (R : V → W → Prop) (f : Tree → List V → V)
    (g : ℕ → List (Tree × W) → W)
    (h : ∀ (l : ℕ) (xs : List (Tree × V × W)), (∀ x ∈ xs, R x.2.1 x.2.2) →
      R (f (RoseTree.node l (xs.map Prod.fst)) (xs.map fun x ↦ x.2.1))
        (g l (xs.map fun x ↦ (x.1, x.2.2))))
    (t : Tree) : R (Const.para f t) (RoseTree.para g t) := by
  refine RoseTree.ind (P := fun t ↦ R (Const.para f t) (RoseTree.para g t)) (fun a cs ih ↦ ?_) t
  have := h a (cs.map fun c ↦ (c, Const.para f c, RoseTree.para g c)) (by simpa using ih)
  rw [Const.para_node, RoseTree.para_node]
  simpa only [List.map_map, Function.comp_def, List.map_id'] using this

end GebTests.Prototypes.FreeTopos.Agreement.Fold

end
