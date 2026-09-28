/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.GoedelT.MirrorEquations

set_option doc.verso true in
/-!
# Primitives at literals written in Geb

The δ rule of the checker of Gödel's T concludes that a primitive applied to literals equals the
literal of its value. The checker in Lean reads that value off the kernel's denotation of the
application; the checker written in Geb computes it from the literals' values by its own table
of the primitives. This module proves the two values equal: {lit}`delta_tree` for results of
the type of trees, {lit}`delta_list` for results of the type of lists of trees.

The proof inverts the checker-evaluator at applications and list nodes
({lit}`infer_app_inv`, {lit}`infer_cons_inv`), reads the value of a quoted tree and of a list
literal ({lit}`lit_tree`, {lit}`lit_list`), and matches each entry of
{name}`Geb.Kernel.prims` with the mirror's primitive of its index.

## Main statements

* {lit}`delta_tree`, {lit}`delta_list` — a primitive applied to literals denotes the mirror's
  value of the primitive at the literals' values.
* {lit}`isLit_label` — the mirror's test of a literal is {name}`Geb.GoedelT.IsLit`.

## Tags

literal, primitive, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.GoedelT.MirrorDelta

open Geb Geb.Kernel Geb.GoedelT GebTests.Prototypes.GoedelT.MirrorTyping
  GebTests.Prototypes.GoedelT.MirrorTerms GebTests.Prototypes.GoedelT.MirrorEquations
open scoped FinEnum

/-- A tree the kernel reads as a function type is that function type. -/
theorem arrow?_eq {F A B : Tree} {h : Ty.den F = (Ty.den A → Ty.den B)}
    (hF : Ty.arrow? F = some ⟨A, B, h⟩) : F = tArrow A B := by
  obtain ⟨⟨a, k⟩, g⟩ := F
  by_cases hak : a = 3 ∧ k = 2
  · obtain ⟨rfl, rfl⟩ := hak
    rw [Ty.arrow?.eq_1] at hF
    cases hF
    exact congrArg (WType.mk (3, 2)) (funext fun i ↦ match i with | 0 => rfl | 1 => rfl)
  · rw [Ty.arrow?.eq_2 _ fun _ h ↦ hak (Prod.mk.inj (mk_index_eq h))] at hF
    cases hF

/-- A tree the kernel reads as a list type is that list type. -/
theorem list?_eq {L A : Tree} {h : Ty.den L = List (Ty.den A)}
    (hL : Ty.list? L = some ⟨A, h⟩) : L = tList A := by
  obtain ⟨⟨a, k⟩, g⟩ := L
  by_cases hak : a = 4 ∧ k = 1
  · obtain ⟨rfl, rfl⟩ := hak
    rw [Ty.list?.eq_1] at hL
    cases hL
    exact congrArg (WType.mk (4, 1)) (funext fun i ↦ match i with | 0 => rfl)
  · rw [Ty.list?.eq_2 _ fun _ h ↦ hak (Prod.mk.inj (mk_index_eq h))] at hL
    cases hL

/-- Function types with equal parts, and only they, are equal. -/
theorem tArrow_inj {A B A' B' : Tree} (h : tArrow A B = tArrow A' B') : A = A' ∧ B = B' := by
  have := congrArg RoseTree.children h
  simp only [tArrow, node2_eq, RoseTree.children_node, List.cons.injEq, and_true] at this
  exact this

/-- List types with equal element types, and only they, are equal. -/
theorem tList_inj {A A' : Tree} (h : tList A = tList A') : A = A' := by
  have := congrArg RoseTree.children h
  simp only [tList_eq, RoseTree.children_node, List.cons.injEq, and_true] at this
  exact this

/-- A list type is not the type of trees. -/
@[simp] theorem tList_ne_tT (A : Tree) : tList A ≠ tT := fun h ↦ by
  have := congrArg RoseTree.label h
  simp [tList_eq, tT, leaf] at this

/-- The children of an application's node, with the application's meaning. -/
theorem infer_app_inv {G : List Glob} {Γ : Ctx} {F X B : Tree} {f : Γ.den → Ty.den B}
    (h : infer G Γ (mk Label.app [F, X]) = some ⟨B, f⟩) :
    ∃ A ff fx, infer G Γ F = some ⟨tArrow A B, ff⟩ ∧ infer G Γ X = some ⟨A, fx⟩ ∧
      ∀ e, f e = ff e (fx e) := by
  rw [mk, infer_node] at h
  simp only [List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨⟨F1, ff⟩, hf, ⟨X1, fx⟩, hx, ⟨A, B', hAB⟩, harr, h⟩ := h
  obtain rfl := arrow?_eq harr
  split at h
  · rename_i hA
    cases hA
    have h' := Sigma.mk.inj_iff.mp (Option.some.inj h)
    obtain rfl := h'.1
    obtain rfl := eq_of_heq h'.2
    exact ⟨_, ff, fx, hf, hx, fun _ ↦ rfl⟩
  · cases h

/-- The children of a list's node, with the list's meaning. -/
theorem infer_cons_inv {G : List Glob} {Γ : Ctx} {x xs A : Tree} {f : Γ.den → Ty.den (tList A)}
    (h : infer G Γ (mk Label.cons [x, xs]) = some ⟨tList A, f⟩) :
    ∃ fx fxs, infer G Γ x = some ⟨A, fx⟩ ∧ infer G Γ xs = some ⟨tList A, fxs⟩ ∧
      ∀ e, f e = fx e :: fxs e := by
  rw [mk, infer_node] at h
  simp only [List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨⟨X1, fx⟩, hx, ⟨L1, fxs⟩, hxs, ⟨A', hA'⟩, hlist, h⟩ := h
  obtain rfl := list?_eq hlist
  split at h
  · rename_i hX
    cases hX
    have h' := Sigma.mk.inj_iff.mp (Option.some.inj h)
    obtain rfl := tList_inj h'.1
    obtain rfl := eq_of_heq h'.2
    exact ⟨fx, fxs, hx, hxs, fun _ ↦ rfl⟩
  · cases h

/-- The type of a list's node is a list type. -/
theorem infer_cons_ty {G : List Glob} {Γ : Ctx} {x xs : Tree} {m : Meaning Γ}
    (h : infer G Γ (mk Label.cons [x, xs]) = some m) : ∃ A, m.1 = tList A := by
  rw [mk, infer_node] at h
  simp only [List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, ⟨A', _⟩, _, h⟩ := h
  split at h
  · cases h
    exact ⟨A', rfl⟩
  · cases h

/-- The meaning of an empty list's node. -/
theorem infer_nil_inv {G : List Glob} {Γ : Ctx} {A : Tree} {m : Meaning Γ}
    (h : infer G Γ (mk Label.nil [A]) = some m) : m = ⟨tList A, fun _ ↦ []⟩ := by
  rw [mk, infer_node] at h
  simp only [List.map_cons, List.map_nil, inferStep] at h
  split at h
  · cases h
    rfl
  · cases h

/-- The label of a function type. -/
@[simp] theorem label_tArrow (A B : Tree) : (tArrow A B).label = Label.tyArrow := by
  rw [tArrow, node2_eq]
  rfl

/-- The label of a list type. -/
@[simp] theorem label_tList (A : Tree) : (tList A).label = Label.tyList := by
  rw [tList_eq]
  rfl

/-- The label of the type of trees. -/
@[simp] theorem label_tT : tT.label = Label.tyTree := rfl

/-- The trees of a list of trees with their values. -/
theorem rtTrees_eq (rs : List (Tree × Tree)) : GebMirror.GoedelT.rtTrees rs = rs.map (·.1) :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [GebMirror.GoedelT.rtTrees, Const.foldr, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The values of a list of trees with their values. -/
theorem rtValues_eq (rs : List (Tree × Tree)) : GebMirror.GoedelT.rtValues rs = rs.map (·.2) :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [GebMirror.GoedelT.rtValues, Const.foldr, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The mirror's disjunction of truth values, as a proposition. -/
theorem or_label (a b : Tree) :
    (GebMirror.GoedelT.or a b).label ≠ 0 ↔ a.label ≠ 0 ∨ b.label ≠ 0 := by
  unfold GebMirror.GoedelT.or
  split <;> simp_all

/-- The mirror's test of a quoted tree. -/
theorem isQuote_label (t : Tree) :
    (GebMirror.GoedelT.isQuote t).label ≠ 0 ↔ t.label = Label.quote ∧ t.children.length = 1 := by
  rw [← RoseTree.node_label_children t]
  simp only [GebMirror.GoedelT.isQuote, and_label, label_node, arity_node, eq_leaf,
    RoseTree.label_node, RoseTree.children_node]

/-- The test of a list literal at a node. -/
theorem isListLit_node (l : ℕ) (cs : List Tree) :
    IsListLit (RoseTree.node l cs) =
      match l, cs.map fun c ↦ (c, IsListLit c) with
      | Label.nil, [_] => true
      | Label.cons, [(x, _), (_, r)] => x.label == Label.quote && x.children.length == 1 && r
      | _, _ => false := by
  rw [IsListLit, RoseTree.para_node]
  rfl

/-- A list literal is the empty list, or a quoted tree in front of a list literal. -/
theorem isListLit_cases {t : Tree} (h : IsListLit t = true) :
    (∃ A, t = mk Label.nil [A]) ∨ ∃ x r, t = mk Label.cons [x, r] ∧ x.label = Label.quote ∧
      x.children.length = 1 ∧ IsListLit r = true := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
    ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩
  rw [isListLit_node] at h
  split at h
  · rename_i heq
    obtain ⟨c, _, rfl, hc, hnil⟩ := List.map_eq_cons_iff.mp heq
    obtain rfl := List.map_eq_nil_iff.mp hnil
    exact Or.inl ⟨c, rfl⟩
  · rename_i x _ _ r heq
    obtain ⟨c, _, rfl, hc, h'⟩ := List.map_eq_cons_iff.mp heq
    obtain ⟨d, _, rfl, hd, hnil⟩ := List.map_eq_cons_iff.mp h'
    obtain rfl := List.map_eq_nil_iff.mp hnil
    obtain ⟨rfl, -⟩ := Prod.mk.inj hc
    obtain ⟨-, rfl⟩ := Prod.mk.inj hd
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact Or.inr ⟨c, d, rfl, h.1.1, h.1.2, h.2⟩
  · cases h

/-- The step of the mirror's elements of a list literal at a node: the node rebuilt, and the
optional node of the elements. -/
def elemsStep (l : Tree) (rs : List (Tree × Tree)) : Tree × Tree :=
  (Const.node l (GebMirror.GoedelT.rtTrees rs),
    if (GebMirror.GoedelT.and (Const.eq l (leaf 19))
        (Const.eq (GebMirror.GoedelT.length (GebMirror.GoedelT.rtTrees rs)) (leaf 1))).label ≠ 0
    then GebMirror.GoedelT.some (Const.node (leaf 0) [])
    else if (GebMirror.GoedelT.and (Const.eq l (leaf 20))
        (Const.eq (GebMirror.GoedelT.length (GebMirror.GoedelT.rtTrees rs)) (leaf 2))).label ≠ 0
    then
      if (GebMirror.GoedelT.and
          (GebMirror.GoedelT.isQuote (GebMirror.GoedelT.at (GebMirror.GoedelT.rtTrees rs) (leaf 0)))
          (GebMirror.GoedelT.isSome
            (GebMirror.GoedelT.at (GebMirror.GoedelT.rtValues rs) (leaf 1)))).label ≠ 0 then
        GebMirror.GoedelT.some (Const.node (leaf 0)
          (Const.child (GebMirror.GoedelT.at (GebMirror.GoedelT.rtTrees rs) (leaf 0)) (leaf 0) ::
            Const.children (GebMirror.GoedelT.get
              (GebMirror.GoedelT.at (GebMirror.GoedelT.rtValues rs) (leaf 1)))))
      else GebMirror.GoedelT.none
    else GebMirror.GoedelT.none)

/-- The mirror's elements of a list literal are the fold of its step. -/
theorem listElems_def (t : Tree) :
    GebMirror.GoedelT.listElems t = (Const.fold elemsStep t).2 := rfl

/-- The fold of the mirror's elements of a list literal gives each tree, and for a list literal
the node of the elements its denotation has at the type of lists of trees, and nothing
otherwise. -/
theorem fold_elemsStep : ∀ t : Tree, (Const.fold elemsStep t).1 = t ∧
    ((Const.fold elemsStep t).2 = enc none ∧ IsListLit t = false ∨
      ∃ vs, (Const.fold elemsStep t).2 = enc (some (RoseTree.node 0 vs)) ∧ IsListLit t = true ∧
        ∀ (G : List Glob) (Γ : Ctx) (f : Γ.den → Ty.den (tList tT)),
          infer G Γ t = some ⟨tList tT, f⟩ → ∀ e, f e = vs) :=
  RoseTree.ind fun l cs ih ↦ by
    rw [fold_node]
    have htr : GebMirror.GoedelT.rtTrees (cs.map (Const.fold elemsStep)) = cs := by
      rw [rtTrees_eq, List.map_map]
      exact (List.map_congr_left fun c hc ↦ (ih c hc).1).trans (List.map_id cs)
    refine ⟨by simp only [elemsStep, htr]; rfl, ?_⟩
    simp only [elemsStep, htr, rtValues_eq, List.map_map, length_eq, eq_leaf, and_label, at_eq]
    split_ifs with h19 h20 hq
    · obtain ⟨rfl, hlen⟩ := h19
      obtain ⟨A, rfl⟩ := List.length_eq_one_iff.mp hlen
      refine Or.inr ⟨[], rfl, rfl, fun G Γ f hf e ↦ ?_⟩
      have := Sigma.mk.inj_iff.mp (infer_nil_inv hf)
      obtain rfl := tList_inj this.1
      rw [eq_of_heq this.2]
      rfl
    · obtain ⟨rfl, hlen⟩ := h20
      obtain ⟨x, r, rfl⟩ := List.length_eq_two.mp hlen
      simp only [List.map_cons, List.map_nil, Function.comp_apply, List.getD_cons_zero,
        List.getD_cons_succ] at hq ⊢
      rw [isQuote_label] at hq
      rcases (ih r (by simp)).2 with ⟨hr, -⟩ | ⟨vs, hr, hlit, hvs⟩
      · rw [hr, isSome_enc] at hq
        exact absurd hq.2 (by simp)
      · refine Or.inr ⟨Const.child x (leaf 0) :: vs, ?_, ?_, fun G Γ f hf e ↦ ?_⟩
        · rw [hr, get_enc, Const.children, RoseTree.children_node]
          rfl
        · simp [isListLit_node, hq.1.1, hq.1.2, hlit]
        · obtain ⟨fx, fxs, hx, hxs, hfe⟩ := infer_cons_inv hf
          obtain ⟨x', hx'⟩ := List.length_eq_one_iff.mp hq.1.2
          have hxq : x = mk Label.quote [x'] := by
            rw [← RoseTree.node_label_children x, hq.1.1, hx']
          subst hxq
          rw [infer_quote] at hx
          obtain rfl := eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj hx)).2
          rw [hfe, hvs G Γ fxs hxs e, child_node]
          rfl
    · obtain ⟨rfl, hlen⟩ := h20
      obtain ⟨x, r, rfl⟩ := List.length_eq_two.mp hlen
      simp only [List.map_cons, List.map_nil, Function.comp_apply, List.getD_cons_zero,
        List.getD_cons_succ, isQuote_label] at hq
      refine Or.inl ⟨rfl, ?_⟩
      simp only [isListLit_node, List.map_cons, List.map_nil, Bool.and_eq_false_iff,
        beq_eq_false_iff_ne]
      rcases (ih r (by simp)).2 with ⟨hr, hlit⟩ | ⟨vs, hr, -, -⟩
      · exact Or.inr hlit
      · rw [hr, isSome_enc] at hq
        simp only [Option.isSome_some, and_true] at hq
        by_cases hl : x.label = Label.quote
        · exact Or.inl (Or.inr fun h ↦ hq ⟨hl, h⟩)
        · exact Or.inl (Or.inl hl)
    · refine Or.inl ⟨rfl, ?_⟩
      rw [isListLit_node]
      split
      · rename_i heq
        exact absurd ⟨rfl, by simpa using congrArg List.length heq⟩ h19
      · rename_i heq
        exact absurd ⟨rfl, by simpa using congrArg List.length heq⟩ h20
      · rfl

/-- The mirror's test of a literal. -/
theorem isLit_label (t : Tree) : (GebMirror.GoedelT.isLit t).label ≠ 0 ↔ IsLit t = true := by
  simp only [GebMirror.GoedelT.isLit, or_label, isQuote_label, IsLit, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, listElems_def]
  rcases (fold_elemsStep t).2 with ⟨h, hl⟩ | ⟨vs, h, hl, -⟩ <;> simp [h, hl, isSome_enc]

/-- A list literal is not a quoted tree. -/
theorem not_quote_of_isListLit {t : Tree} (h : IsListLit t = true) :
    ¬(t.label = Label.quote ∧ t.children.length = 1) := by
  rcases isListLit_cases h with ⟨A, rfl⟩ | ⟨x, r, rfl, -⟩ <;>
    simp [Label.nil, Label.cons, Label.quote]

/-- The value of a literal at the type of trees is the mirror's value of the literal. -/
theorem lit_tree {G : List Glob} {Γ : Ctx} {a : Tree} {f : Γ.den → Ty.den tT}
    (ha : IsLit a = true) (h : infer G Γ a = some ⟨tT, f⟩) (e : Γ.den) :
    f e = GebMirror.GoedelT.litValue a := by
  simp only [IsLit, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at ha
  rcases ha with ⟨hl, hlen⟩ | hlist
  · obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    have hq : a = mk Label.quote [x] := by rw [← RoseTree.node_label_children a, hl, hx]
    subst hq
    rw [infer_quote] at h
    obtain rfl := eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
    change x = GebMirror.GoedelT.litValue (mk Label.quote [x])
    simp [GebMirror.GoedelT.litValue, isQuote_label, child_node]
  · rcases isListLit_cases hlist with ⟨A, rfl⟩ | ⟨x, r, rfl, -⟩
    · exact absurd (Sigma.mk.inj_iff.mp (infer_nil_inv h)).1 (tList_ne_tT A).symm
    · obtain ⟨A, hA⟩ := infer_cons_ty h
      exact absurd hA (tList_ne_tT A).symm

/-- The value of a literal at the type of lists of trees is the list of children of the mirror's
value of the literal. -/
theorem lit_list {G : List Glob} {Γ : Ctx} {a : Tree} {f : Γ.den → Ty.den (tList tT)}
    (ha : IsLit a = true) (h : infer G Γ a = some ⟨tList tT, f⟩) (e : Γ.den) :
    f e = (GebMirror.GoedelT.litValue a).children := by
  simp only [IsLit, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at ha
  rcases ha with ⟨hl, hlen⟩ | hlist
  · obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    have hq : a = mk Label.quote [x] := by rw [← RoseTree.node_label_children a, hl, hx]
    subst hq
    rw [infer_quote] at h
    exact absurd (Sigma.mk.inj_iff.mp (Option.some.inj h)).1 (tList_ne_tT tT).symm
  · have hv : GebMirror.GoedelT.litValue a =
        GebMirror.GoedelT.get (GebMirror.GoedelT.listElems a) := by
      simp [GebMirror.GoedelT.litValue, isQuote_label, not_quote_of_isListLit hlist]
    rw [hv, listElems_def]
    rcases (fold_elemsStep a).2 with ⟨-, hl⟩ | ⟨vs, hv', -, hvs⟩
    · rw [hl] at hlist
      cases hlist
    · rw [hv', get_enc, RoseTree.children_node, hvs G Γ f h e]

/-- Function types are equal exactly when their parts are. -/
theorem tArrow_eq_iff {A B A' B' : Tree} : tArrow A B = tArrow A' B' ↔ A = A' ∧ B = B' :=
  ⟨tArrow_inj, fun ⟨h, h'⟩ ↦ h ▸ h' ▸ rfl⟩

/-- A function type is not the type of trees. -/
@[simp] theorem tArrow_ne_tT (A B : Tree) : tArrow A B ≠ tT := fun h ↦ by
  simpa using congrArg RoseTree.label h

/-- The type of trees is not a function type. -/
@[simp] theorem tT_ne_tArrow (A B : Tree) : tT ≠ tArrow A B := fun h ↦ tArrow_ne_tT A B h.symm

/-- A list type is not a function type. -/
@[simp] theorem tList_ne_tArrow (A B C : Tree) : tList A ≠ tArrow B C := fun h ↦ by
  simpa using congrArg RoseTree.label h

/-- A function type is not a list type. -/
@[simp] theorem tArrow_ne_tList (A B C : Tree) : tArrow B C ≠ tList A := fun h ↦
  tList_ne_tArrow A B C h.symm

/-- The type of trees is not a list type. -/
@[simp] theorem tT_ne_tList (A : Tree) : tT ≠ tList A := fun h ↦ tList_ne_tT A h.symm

/-- The primitive of a primitive's node in the empty context, with its meaning. -/
theorem infer_prim_inv {G : List Glob} {k : Tree} {m : Meaning []}
    (h : infer G [] (mk Label.prim [k]) = some m) : prims[k.label]? = some ⟨m.1, m.2 ()⟩ := by
  rw [mk, infer_node] at h
  simp only [List.map_cons, List.map_nil, inferStep] at h
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
  exact hg

/-- No primitive is a tree or a list of trees. -/
theorem prim0_ne {i : ℕ} {T : Tree} {g : Ty.den T} (h : prims[i]? = some ⟨T, g⟩) :
    T ≠ tT ∧ T ≠ tList tT := by
  match i, h with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h | 9, h | 10, h | 11, h | 12, h
  | 13, h =>
    rw [← (Sigma.mk.inj_iff.mp (Option.some.inj h)).1]
    simp
  | _ + 14, h => simp [prims] at h

/-- Every primitive takes a tree first. -/
theorem prim_arg {i : ℕ} {A B : Tree} {g : Ty.den (tArrow A B)}
    (h : prims[i]? = some ⟨tArrow A B, g⟩) : A = tT := by
  match i, h with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h | 9, h | 10, h | 11, h | 12, h
  | 13, h => exact (tArrow_inj (Sigma.mk.inj_iff.mp (Option.some.inj h)).1).1.symm
  | _ + 14, h => simp [prims] at h

/-- A primitive from trees to trees is the mirror's primitive of its index. -/
theorem prim1_tree {i : ℕ} {g : Ty.den (tArrow tT tT)} (h : prims[i]? = some ⟨tArrow tT tT, g⟩)
    (x y : Tree) : g x = GebMirror.GoedelT.delta (leaf i) x y := by
  match i, h with
  | 0, h | 1, h | 13, h =>
    obtain rfl := eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
    rfl
  | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h | 9, h | 10, h | 11, h | 12, h =>
    exact absurd (Sigma.mk.inj_iff.mp (Option.some.inj h)).1 (by simp [tArrow_eq_iff])
  | _ + 14, h => simp [prims] at h

/-- A primitive from trees to lists of trees is the children of the mirror's primitive of its
index. -/
theorem prim1_list {i : ℕ} {g : Ty.den (tArrow tT (tList tT))}
    (h : prims[i]? = some ⟨tArrow tT (tList tT), g⟩) (x y : Tree) :
    g x = (GebMirror.GoedelT.delta (leaf i) x y).children := by
  match i, h with
  | 4, h =>
    obtain rfl := eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
    change Const.children x = (Const.node (leaf 0) (Const.children x)).children
    rw [Const.node, RoseTree.children_node]
  | 0, h | 1, h | 2, h | 3, h | 5, h | 6, h | 7, h | 8, h | 9, h | 10, h | 11, h | 12, h
  | 13, h => exact absurd (Sigma.mk.inj_iff.mp (Option.some.inj h)).1 (by simp [tArrow_eq_iff])
  | _ + 14, h => simp [prims] at h

/-- A primitive of two arguments takes a tree or a list of trees second. -/
theorem prim2_arg {i : ℕ} {A B : Tree} {g : Ty.den (tArrow tT (tArrow A B))}
    (h : prims[i]? = some ⟨tArrow tT (tArrow A B), g⟩) : A = tT ∨ A = tList tT := by
  match i, h with
  | 2, h | 5, h | 6, h | 7, h | 8, h | 9, h | 10, h | 11, h | 12, h =>
    exact Or.inl (tArrow_inj (tArrow_inj (Sigma.mk.inj_iff.mp (Option.some.inj h)).1).2).1.symm
  | 3, h =>
    exact Or.inr (tArrow_inj (tArrow_inj (Sigma.mk.inj_iff.mp (Option.some.inj h)).1).2).1.symm
  | 0, h | 1, h | 4, h | 13, h =>
    exact absurd (Sigma.mk.inj_iff.mp (Option.some.inj h)).1 (by simp [tArrow_eq_iff])
  | _ + 14, h => simp [prims] at h

/-- A primitive of two trees to a tree is the mirror's primitive of its index. -/
theorem prim2_tree {i : ℕ} {g : Ty.den (tArrow tT (tArrow tT tT))}
    (h : prims[i]? = some ⟨tArrow tT (tArrow tT tT), g⟩) (x y : Tree) :
    g x y = GebMirror.GoedelT.delta (leaf i) x y := by
  match i, h with
  | 2, h | 5, h | 6, h | 7, h | 8, h | 9, h | 10, h | 11, h | 12, h =>
    obtain rfl := eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
    rfl
  | 0, h | 1, h | 3, h | 4, h | 13, h =>
    exact absurd (Sigma.mk.inj_iff.mp (Option.some.inj h)).1 (by simp [tArrow_eq_iff])
  | _ + 14, h => simp [prims] at h

/-- A primitive of a tree and a list of trees to a tree is the mirror's primitive of its index,
at the node of the list. -/
theorem prim2_list {i : ℕ} {g : Ty.den (tArrow tT (tArrow (tList tT) tT))}
    (h : prims[i]? = some ⟨tArrow tT (tArrow (tList tT) tT), g⟩) (x y : Tree) :
    g x y.children = GebMirror.GoedelT.delta (leaf i) x y := by
  match i, h with
  | 3, h =>
    obtain rfl := eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
    rfl
  | 0, h | 1, h | 2, h | 4, h | 5, h | 6, h | 7, h | 8, h | 9, h | 10, h | 11, h | 12, h
  | 13, h => exact absurd (Sigma.mk.inj_iff.mp (Option.some.inj h)).1 (by simp [tArrow_eq_iff])
  | _ + 14, h => simp [prims] at h

/-- No primitive of two arguments gives a list. -/
theorem prim2_none {i : ℕ} {A : Tree} {g : Ty.den (tArrow tT (tArrow A (tList tT)))}
    (h : prims[i]? = some ⟨tArrow tT (tArrow A (tList tT)), g⟩) : False := by
  match i, h with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h | 9, h | 10, h | 11, h | 12, h
  | 13, h => exact absurd (Sigma.mk.inj_iff.mp (Option.some.inj h)).1 (by simp [tArrow_eq_iff])
  | _ + 14, h => simp [prims] at h

/-- No primitive takes three arguments. -/
theorem prim3_none {i : ℕ} {A C D : Tree} {g : Ty.den (tArrow tT (tArrow A (tArrow C D)))}
    (h : prims[i]? = some ⟨tArrow tT (tArrow A (tArrow C D)), g⟩) : False := by
  match i, h with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h | 9, h | 10, h | 11, h | 12, h
  | 13, h => exact absurd (Sigma.mk.inj_iff.mp (Option.some.inj h)).1 (by simp [tArrow_eq_iff])
  | _ + 14, h => simp [prims] at h

/-- A term applied to arguments has a meaning only where the term does. -/
theorem infer_apps_inv {G : List Glob} {Γ : Ctx} (xs : List Tree) :
    ∀ (F : Tree) (m : Meaning Γ), infer G Γ (apps F xs) = some m → ∃ m', infer G Γ F = some m' :=
  xs.rec (fun _ m h ↦ ⟨m, h⟩) fun x _ ih F m h ↦ by
    obtain ⟨⟨_, _⟩, h'⟩ := ih (mk Label.app [F, x]) m h
    obtain ⟨_, _, _, hF, -⟩ := infer_app_inv h'
    exact ⟨_, hF⟩

/-- A primitive applied to three or more arguments has no meaning. -/
theorem infer_prim3 {G : List Glob} {k a b c : Tree} {rest : List Tree} {m : Meaning []}
    (h : infer G [] (apps (mk Label.prim [k]) (a :: b :: c :: rest)) = some m) : False := by
  obtain ⟨⟨_, _⟩, h3⟩ := infer_apps_inv rest _ m h
  obtain ⟨_, _, _, h2, -⟩ := infer_app_inv h3
  obtain ⟨_, _, _, h1, -⟩ := infer_app_inv h2
  obtain ⟨_, _, _, hp, -⟩ := infer_app_inv h1
  have hp' := infer_prim_inv hp
  obtain rfl := prim_arg hp'
  exact prim3_none hp'

/-- A primitive applied to literals, at the type of trees, is the mirror's primitive of its
index at the literals' values. -/
theorem delta_tree {G : List Glob} {k : Tree} {args : List Tree} {f : Ctx.den [] → Ty.den tT}
    (hargs : ∀ a ∈ args, IsLit a = true)
    (h : infer G [] (apps (mk Label.prim [k]) args) = some ⟨tT, f⟩) (e : Ctx.den []) :
    f e = GebMirror.GoedelT.delta (Const.label k)
      (GebMirror.GoedelT.litValue (args.getD 0 (leaf 0)))
      (GebMirror.GoedelT.litValue (args.getD 1 (leaf 0))) := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact absurd rfl (prim0_ne (infer_prim_inv h)).1
  · obtain ⟨A, ff, fx, hp, ha, hf⟩ := infer_app_inv h
    have hp' := infer_prim_inv hp
    obtain rfl := prim_arg hp'
    simp only [hf, lit_tree (hargs a (by simp)) ha]
    exact prim1_tree hp' _ _
  · obtain ⟨B, ff, fb, hab, hb, hf⟩ := infer_app_inv h
    obtain ⟨A, fp, fa, hp, ha, hff⟩ := infer_app_inv hab
    have hp' := infer_prim_inv hp
    obtain rfl := prim_arg hp'
    rcases prim2_arg hp' with rfl | rfl
    · simp only [hf, hff, lit_tree (hargs a (by simp)) ha, lit_tree (hargs b (by simp)) hb]
      exact prim2_tree hp' _ _
    · simp only [hf, hff, lit_tree (hargs a (by simp)) ha, lit_list (hargs b (by simp)) hb]
      exact prim2_list hp' _ _
  · exact (infer_prim3 h).elim

/-- A primitive applied to literals, at the type of lists of trees, is the children of the
mirror's primitive of its index at the literals' values. -/
theorem delta_list {G : List Glob} {k : Tree} {args : List Tree}
    {f : Ctx.den [] → Ty.den (tList tT)} (hargs : ∀ a ∈ args, IsLit a = true)
    (h : infer G [] (apps (mk Label.prim [k]) args) = some ⟨tList tT, f⟩) (e : Ctx.den []) :
    f e = (GebMirror.GoedelT.delta (Const.label k)
      (GebMirror.GoedelT.litValue (args.getD 0 (leaf 0)))
      (GebMirror.GoedelT.litValue (args.getD 1 (leaf 0)))).children := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact absurd rfl (prim0_ne (infer_prim_inv h)).2
  · obtain ⟨A, ff, fx, hp, ha, hf⟩ := infer_app_inv h
    have hp' := infer_prim_inv hp
    obtain rfl := prim_arg hp'
    simp only [hf, lit_tree (hargs a (by simp)) ha]
    exact prim1_list hp' _ _
  · obtain ⟨B, ff, fb, hab, hb, hf⟩ := infer_app_inv h
    obtain ⟨A, fp, fa, hp, ha, hff⟩ := infer_app_inv hab
    have hp' := infer_prim_inv hp
    obtain rfl := prim_arg hp'
    exact (prim2_none hp').elim
  · exact (infer_prim3 h).elim

/-- The body of an abstraction's node, with the abstraction's type. -/
theorem infer_lam_inv {G : List Glob} {Γ : Ctx} {A b T : Tree} {f : Γ.den → Ty.den T}
    (h : infer G Γ (mk Label.lam [A, b]) = some ⟨T, f⟩) :
    ∃ B fb, T = tArrow A B ∧ infer G (A :: Γ) b = some ⟨B, fb⟩ := by
  rw [mk, infer_node] at h
  simp only [List.map_cons, List.map_nil, inferStep] at h
  split at h
  · obtain ⟨⟨B, fb⟩, hb, hm⟩ := Option.map_eq_some_iff.mp h
    exact ⟨B, fb, (congrArg Sigma.fst hm).symm, hb⟩
  · cases h

end GebTests.Prototypes.GoedelT.MirrorDelta

end
