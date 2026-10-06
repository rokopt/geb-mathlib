/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Check
public import Geb.Prototypes.Kernel.Subst

set_option doc.verso true in
/-!
# The type checker written in Geb decides as the kernel's

The kernel's checker written in Geb, {lit}`bootstrap/check.geb`, gives the type of a term in a
global environment's types and a context, as the reader represents an optional tree:
{lit}`enc`. Its Lean mirror, {lit}`«Check.typeIn»`, emitted by the bootstrap compiler,
is here proved equal to the type the kernel's checker-evaluator {name}`Geb.Kernel.infer` gives,
at every term: {lit}`typeIn_eq`.

The proof follows the mirror's fold over the term. At each node, the mirror's test of the label
and the number of children selects one of the kernel's rules, and a lemma per rule states that
the mirror's branch gives the type {name}`Geb.Kernel.inferStep` gives there, from the children's
types; nodes of a label or arity no rule has give nothing on both sides.

## Main definitions

* {lit}`enc` — an optional tree as the reader represents it.
* {lit}`tyOf` — the optional type of a term, as the checker-evaluator gives it.

## Main statements

* {lit}`typeIn_eq` — the mirror's type of a term is the checker-evaluator's.
* {lit}`infer_app_inv`, {lit}`infer_lam_inv` — the checker-evaluator's meaning of an application
  and the type of an abstraction, from their children's.

## Tags

type checking, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Check

namespace GebTests.Prototypes.CheckMirror

open Geb Geb.Kernel
open scoped FinEnum

/-- An optional tree as the reader represents it: nothing is the leaf of label zero, and a tree
is the node of label one over it. -/
def enc : Option Tree → Tree
  | some t => RoseTree.node 1 [t]
  | none => leaf 0

/-- The mirror's {lit}`some`. -/
theorem some_eq (t : Tree) : «Prelude.some» t = enc (some t) := rfl

/-- The mirror's {lit}`none`. -/
theorem none_eq : «Prelude.none» = enc none := rfl

/-- The label of a leaf. -/
@[simp] theorem label_leaf (n : ℕ) : (leaf n).label = n := rfl

/-- The mirror's test of an optional tree. -/
theorem isSome_enc (o : Option Tree) :
    («Prelude.isSome» (enc o)).label ≠ 0 ↔ o.isSome := by
  cases o <;> simp [«Prelude.isSome», enc, Const.eq, Const.label, ofBool]

/-- A node's child by index, the leaf of label zero when out of range. -/
theorem child_node (l i : ℕ) (cs : List Tree) :
    Const.child (RoseTree.node l cs) (leaf i) = cs.getD i (leaf 0) := by
  change (if h : i < cs.length then cs.toArray[i] else leaf 0) = cs.getD i (leaf 0)
  split
  · simp_all
  · rename_i h
    simp [List.getElem?_eq_none (Nat.le_of_not_lt h)]

/-- The mirror's tree of a present optional tree. -/
theorem get_enc (t : Tree) : «Prelude.get» (enc (some t)) = t := by
  simp [«Prelude.get», enc, child_node]

/-- The mirror's length of a list. -/
theorem length_eq (xs : List Tree) : «Prelude.length» xs = leaf xs.length :=
  xs.rec rfl fun _ _ ih ↦ by
    simp only [«Prelude.length», Const.foldr, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The mirror's element of a list at a position, the leaf of label zero when out of range. -/
theorem at_eq (xs : List Tree) (i : ℕ) : «Prelude.at» xs (leaf i) = xs.getD i (leaf 0) :=
  child_node 0 i xs

/-- The comparison of two labels' equality. -/
theorem eq_leaf (a b : ℕ) : (Const.eq (leaf a) (leaf b)).label ≠ 0 ↔ a = b := by
  by_cases h : a = b <;> simp [Const.eq, ofBool, h]

/-- The comparison of two labels' order. -/
theorem lt_leaf (a b : ℕ) : (Const.lt (leaf a) (leaf b)).label ≠ 0 ↔ a < b := by
  by_cases h : a < b <;> simp [Const.lt, ofBool, h]

/-- The mirror's element of a list at a position, when the position is in range. -/
theorem nth_eq (xs : List Tree) (i : ℕ) : «Prelude.nth» xs (leaf i) = enc xs[i]? := by
  simp only [«Prelude.nth», length_eq]
  split
  · rename_i h
    rw [lt_leaf] at h
    rw [some_eq, at_eq]
    simp [h]
  · rename_i h
    rw [lt_leaf] at h
    rw [none_eq, List.getElem?_eq_none (Nat.le_of_not_lt h)]

/-- The trees of a list of trees with their results. -/
theorem rrTrees_eq (rs : List (Tree × (List Tree → Tree))) :
    «Reader.rrTrees» rs = rs.map (·.1) :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«Reader.rrTrees», Const.foldr, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- Dropping the head of a list as many times as a label. -/
theorem repeat_tail (rs : List (Tree × (List Tree → Tree))) :
    ∀ i : ℕ, Nat.repeat «Reader/RRs.tail» i rs = rs.drop i :=
  Nat.rec rfl fun i ih ↦ by
    rw [Nat.repeat, ih, ← List.tail_drop]
    cases rs.drop i <;> rfl

/-- The mirror's result of a child at a position, applied to a context; nothing when the
position is out of range. -/
theorem rrAt_eq (rs : List (Tree × (List Tree → Tree))) (i : ℕ) (Γ : List Tree) :
    «Reader.rrAt» rs (leaf i) Γ = (rs[i]?.map (·.2 Γ)).getD (enc none) := by
  simp only [«Reader.rrAt», Const.iter, label_leaf, repeat_tail, Const.lcase]
  cases h : rs.drop i with
  | nil =>
    rw [List.drop_eq_nil_iff] at h
    simp [List.getElem?_eq_none h, none_eq]
  | cons r _ =>
    have : rs[i]? = some r := by
      rw [← List.head?_drop, h]
      rfl
    simp [this]

/-- A node of two children is the node of their list. -/
theorem node2_eq (l : ℕ) (a b : Tree) : node2 l a b = RoseTree.node l [a, b] := by
  refine (RoseTree.node_eq_mk l [a, b] rfl ![a, b] fun i ↦ ?_).symm
  match i with
  | 0 => rfl
  | 1 => rfl

/-- The list type is the node of its element type. -/
theorem tList_eq (A : Tree) : tList A = RoseTree.node Label.tyList [A] := by
  refine (RoseTree.node_eq_mk Label.tyList [A] rfl ![A] fun i ↦ ?_).symm
  match i with
  | 0 => rfl

/-- The mirror's function type. -/
theorem tyArrow_eq (A B : Tree) : «Check.tyArrow» A B = tArrow A B := by
  rw [tArrow, node2_eq]
  rfl

/-- The mirror's list type. -/
theorem tyList_eq (A : Tree) : «Check.tyList» A = tList A := by
  rw [tList_eq]
  rfl

/-- The mirror's product type, as the node of two children. -/
theorem node2_mirror (l : ℕ) (A B : Tree) :
    «Reader.node2» (leaf l) A B = node2 l A B := by
  rw [node2_eq]
  rfl

/-- The fold of trees at a node. -/
theorem fold_node {α : Type} (f : Tree → List α → α) (l : ℕ) (cs : List Tree) :
    Const.fold f (RoseTree.node l cs) = f (leaf l) (cs.map (Const.fold f)) := by
  simp [Const.fold, RoseTree.elim_node]

/-- The truth value of a Boolean has label zero exactly when it is false. -/
@[simp] theorem ofBool_label (b : Bool) : (ofBool b).label ≠ 0 ↔ b = true := by
  cases b <;> simp [ofBool]

/-- The mirror's conjunction of truth values. -/
theorem and_ofBool (a b : Bool) :
    «Prelude.and» (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- The comparison of two labels' equality, as a truth value. -/
theorem eq_leaf_ofBool (a b : ℕ) : Const.eq (leaf a) (leaf b) = ofBool (a == b) := rfl

/-- The test of a type at a node. -/
theorem isTy_node (l : ℕ) (cs : List Tree) :
    Ty.IsTy (RoseTree.node l cs) =
      match l, cs.map Ty.IsTy with
      | Label.tyTree, [] | Label.tyUnit, [] => true
      | Label.tyProd, [a, b] | Label.tyArrow, [a, b] => a && b
      | Label.tyList, [a] => a
      | _, _ => false := by
  rw [Ty.IsTy, RoseTree.elim_node]
  rfl

/-- The mirror's test of a type. -/
theorem isTy_eq : ∀ t : Tree, «Check.isTy» t = ofBool (Ty.IsTy t) :=
  RoseTree.ind fun l cs ih ↦ by
    unfold «Check.isTy» at ih ⊢
    rw [fold_node, List.map_congr_left ih, isTy_node]
    rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · match l with
      | 0 | 1 => rfl
      | _ + 2 => simp [Const.eq, ofBool, length_eq]
    · match l with
      | 0 | 1 | 2 | 3 | 4 | _ + 5 => rfl
    · simp only [List.map_cons, List.map_nil]
      match l with
      | 2 | 3 => cases Ty.IsTy a <;> cases Ty.IsTy b <;> rfl
      | 0 | 1 | 4 | _ + 5 => rfl
    · match l with
      | 0 | 1 | 2 | 3 | 4 | _ + 5 => rfl

/-- The label of a node, as the kernel's primitive gives it. -/
theorem label_node (l : ℕ) (cs : List Tree) : Const.label (RoseTree.node l cs) = leaf l := rfl

/-- The number of a node's children, as the kernel's primitive gives it. -/
theorem arity_node (l : ℕ) (cs : List Tree) :
    Const.arity (RoseTree.node l cs) = leaf cs.length := rfl

/-- The children of a node, as the kernel's primitive gives them. -/
theorem children_node (l : ℕ) (cs : List Tree) : Const.children (RoseTree.node l cs) = cs :=
  RoseTree.children_node l cs

/-- The label and the number of children of a tree built by its constructor. -/
theorem mk_index_eq {x y : ℕ × ℕ} {g : RoseTree.Sig ℕ x → Tree} {g' : RoseTree.Sig ℕ y → Tree}
    (h : WType.mk x g = WType.mk y g') : x = y :=
  congrArg (fun t : Tree ↦ match t with | WType.mk x _ => x) h

/-- A tree the kernel reads as a function type passes the mirror's test, with the parts it
reads. -/
theorem arrow_some {F A B : Tree} {h : Ty.den F = (Ty.den A → Ty.den B)}
    (hF : Ty.arrow? F = some ⟨A, B, h⟩) :
    («Check.isArrow» F).label ≠ 0 ∧ Const.child F (leaf 0) = A ∧
      Const.child F (leaf 1) = B := by
  obtain ⟨⟨a, k⟩, g⟩ := F
  by_cases hak : a = 3 ∧ k = 2
  · obtain ⟨rfl, rfl⟩ := hak
    rw [Ty.arrow?.eq_1] at hF
    cases hF
    exact ⟨Nat.one_ne_zero, rfl, rfl⟩
  · rw [Ty.arrow?.eq_2 _ fun _ h ↦ hak (Prod.mk.inj (mk_index_eq h))] at hF
    cases hF

/-- A tree the kernel does not read as a function type fails the mirror's test. -/
theorem arrow_none {F : Tree} (hF : Ty.arrow? F = none) :
    («Check.isArrow» F).label = 0 := by
  obtain ⟨⟨a, k⟩, g⟩ := F
  change («Prelude.and» (ofBool (a == 3)) (ofBool (k == 2))).label = 0
  rw [and_ofBool]
  by_cases hak : a = 3 ∧ k = 2
  · obtain ⟨rfl, rfl⟩ := hak
    rw [Ty.arrow?.eq_1] at hF
    cases hF
  · by_cases ha : a = 3
    · simp [ha, show k ≠ 2 from fun hk ↦ hak ⟨ha, hk⟩, ofBool]
    · simp [ha, ofBool]

/-- The mirror's product type of two optional types. -/
theorem some2_eq (l : ℕ) (a b : Option Tree) :
    «Reader.some2» (leaf l) (enc a) (enc b) =
      enc (do let A ← a; let B ← b; some (node2 l A B)) := by
  cases a <;> cases b
  · rfl
  · rfl
  · rfl
  · simp only [node2_eq]
    rfl

/-- The mirror's types of the primitives are the kernel's. -/
theorem primTypes_eq : «Check.primTypes» = prims.map (·.1) := by
  decide +kernel

/-- The type of a variable of a context is the context's type at its index. -/
theorem var_map_fst : ∀ (Γ : Ctx) (n : ℕ), (Γ.var n).map (·.1) = Γ[n]? :=
  List.rec (fun _ ↦ rfl) fun A Γ ih n ↦ Nat.casesOn n rfl fun m ↦ by
    simp only [Ctx.var, Option.map_map, List.getElem?_cons_succ] at ih ⊢
    exact ih m

/-- The type of a meaning, or nothing. -/
abbrev fstOf {Γ : Ctx} (o : Option (Meaning Γ)) : Option Tree := o.map (·.1)

/-- The optional type of a term in a context, as the checker-evaluator gives it. -/
def tyOf (G : List Glob) (Γ : Ctx) (t : Tree) : Option Tree := fstOf (infer G Γ t)

/-- The children of a node with their types, as the mirror's fold gives them. -/
def withTys (G : List Glob) (cs : List Tree) : List (Tree × (List Tree → Tree)) :=
  cs.map fun c ↦ (c, fun Γ ↦ enc (tyOf G Γ c))

/-- The type of a node, from its label and its children with their meanings. -/
theorem tyOf_node (G : List Glob) (Γ : Ctx) (l : ℕ) (cs : List Tree) :
    tyOf G Γ (RoseTree.node l cs) =
      fstOf (inferStep l (cs.map fun c ↦ (c, RoseTree.para inferStep c)) G Γ) := by
  simp only [tyOf, infer, RoseTree.para_node]

/-- The type an abstraction's node gives. -/
theorem inferStep_lam (G : List Glob) (Γ : Ctx) (A b : Tree) (sA sb : Sem) :
    fstOf (inferStep Label.lam [(A, sA), (b, sb)] G Γ) =
      if Ty.IsTy A then (fstOf (sb G (A :: Γ))).map (tArrow A) else none := by
  simp only [inferStep, Label.lam]
  cases Ty.IsTy A <;> simp [fstOf, Option.map_map, Function.comp_def]

/-- The type an application's node gives. -/
theorem inferStep_app (G : List Glob) (Γ : Ctx) (f x : Tree) (sf sx : Sem) :
    fstOf (inferStep Label.app [(f, sf), (x, sx)] G Γ) =
      (fstOf (sf G Γ)).bind fun F ↦ (fstOf (sx G Γ)).bind fun X ↦
        (Ty.arrow? F).bind fun p ↦ if X = p.1 then some p.2.1 else none := by
  simp only [inferStep, Label.app]
  cases sf G Γ with
  | none => rfl
  | some mf =>
    cases sx G Γ with
    | none => rfl
    | some mx =>
      simp only [fstOf, Option.bind_eq_bind, Option.bind_some, Option.map_some]
      rcases Ty.arrow? mf.1 with _ | ⟨A, B, h⟩
      · rfl
      · simp only [Option.bind_some]
        split <;> simp_all

/-- The type a variable's node gives. -/
theorem inferStep_var (G : List Glob) (Γ : Ctx) (n : Tree) (sn : Sem) :
    fstOf (inferStep Label.var [(n, sn)] G Γ) = Γ[n.label]? := by
  simp only [inferStep, Label.var]
  exact var_map_fst Γ n.label

/-- The type a pair's node gives. -/
theorem inferStep_pair (G : List Glob) (Γ : Ctx) (a b : Tree) (sa sb : Sem) :
    fstOf (inferStep Label.pair [(a, sa), (b, sb)] G Γ) =
      (fstOf (sa G Γ)).bind fun A ↦ (fstOf (sb G Γ)).bind fun B ↦ some (tProd A B) := by
  simp only [inferStep, Label.pair]
  cases sa G Γ <;> cases sb G Γ <;> rfl

/-- The type a first projection's node gives. -/
theorem inferStep_fst (G : List Glob) (Γ : Ctx) (p : Tree) (sp : Sem) :
    fstOf (inferStep Label.fst [(p, sp)] G Γ) =
      (fstOf (sp G Γ)).bind fun P ↦ (Ty.prod? P).map (·.1) := by
  simp only [inferStep, Label.fst]
  cases sp G Γ with
  | none => rfl
  | some mp =>
    simp only [fstOf, Option.bind_eq_bind, Option.bind_some, Option.map_some]
    rcases Ty.prod? mp.1 with _ | ⟨A, B, h⟩ <;> rfl

/-- The type a second projection's node gives. -/
theorem inferStep_snd (G : List Glob) (Γ : Ctx) (p : Tree) (sp : Sem) :
    fstOf (inferStep Label.snd [(p, sp)] G Γ) =
      (fstOf (sp G Γ)).bind fun P ↦ (Ty.prod? P).map (·.2.1) := by
  simp only [inferStep, Label.snd]
  cases sp G Γ with
  | none => rfl
  | some mp =>
    simp only [fstOf, Option.bind_eq_bind, Option.bind_some, Option.map_some]
    rcases Ty.prod? mp.1 with _ | ⟨A, B, h⟩ <;> rfl

/-- The type a conditional's node gives. -/
theorem inferStep_cond (G : List Glob) (Γ : Ctx) (c a b : Tree) (sc sa sb : Sem) :
    fstOf (inferStep Label.cond [(c, sc), (a, sa), (b, sb)] G Γ) =
      (fstOf (sc G Γ)).bind fun C ↦ (fstOf (sa G Γ)).bind fun A ↦ (fstOf (sb G Γ)).bind fun B ↦
        if C = tT then if B = A then some A else none else none := by
  simp only [inferStep, Label.cond]
  cases sc G Γ with
  | none => rfl
  | some mc =>
    cases sa G Γ with
    | none => rfl
    | some ma =>
      cases sb G Γ with
      | none => rfl
      | some mb =>
        simp only [fstOf, Option.bind_eq_bind, Option.bind_some, Option.map_some]
        split <;> [split <;> simp_all; simp_all]

/-- The type a list construction's node gives. -/
theorem inferStep_cons (G : List Glob) (Γ : Ctx) (x xs : Tree) (sx sxs : Sem) :
    fstOf (inferStep Label.cons [(x, sx), (xs, sxs)] G Γ) =
      (fstOf (sx G Γ)).bind fun X ↦ (fstOf (sxs G Γ)).bind fun L ↦
        (Ty.list? L).bind fun p ↦ if X = p.1 then some (tList p.1) else none := by
  simp only [inferStep, Label.cons]
  cases sx G Γ with
  | none => rfl
  | some mx =>
    cases sxs G Γ with
    | none => rfl
    | some mxs =>
      simp only [fstOf, Option.bind_eq_bind, Option.bind_some, Option.map_some]
      rcases Ty.list? mxs.1 with _ | ⟨A, h⟩
      · rfl
      · simp only [Option.bind_some]
        split <;> simp_all

/-- The type a primitive's node gives. -/
theorem inferStep_prim (G : List Glob) (Γ : Ctx) (k : Tree) (sk : Sem) :
    fstOf (inferStep Label.prim [(k, sk)] G Γ) = (prims.map (·.1))[k.label]? := by
  simp only [inferStep, Label.prim, fstOf, Option.map_map, List.getElem?_map]
  rfl

/-- The type a reference's node gives. -/
theorem inferStep_ref (G : List Glob) (Γ : Ctx) (n : Tree) (sn : Sem) :
    fstOf (inferStep Label.ref [(n, sn)] G Γ) = (G.map (·.1))[n.label]? := by
  simp only [inferStep, Label.ref, fstOf, Option.map_map, List.getElem?_map]
  rfl

/-- A tree the kernel reads as a product type passes the mirror's test, with the parts it
reads. -/
theorem prod_some {P A B : Tree} {h : Ty.den P = (Ty.den A × Ty.den B)}
    (hP : Ty.prod? P = some ⟨A, B, h⟩) :
    («Check.isProd» P).label ≠ 0 ∧ Const.child P (leaf 0) = A ∧
      Const.child P (leaf 1) = B := by
  obtain ⟨⟨a, k⟩, g⟩ := P
  by_cases hak : a = 2 ∧ k = 2
  · obtain ⟨rfl, rfl⟩ := hak
    rw [Ty.prod?.eq_1] at hP
    cases hP
    exact ⟨Nat.one_ne_zero, rfl, rfl⟩
  · rw [Ty.prod?.eq_2 _ fun _ h ↦ hak (Prod.mk.inj (mk_index_eq h))] at hP
    cases hP

/-- A tree the kernel does not read as a product type fails the mirror's test. -/
theorem prod_none {P : Tree} (hP : Ty.prod? P = none) :
    («Check.isProd» P).label = 0 := by
  obtain ⟨⟨a, k⟩, g⟩ := P
  change («Prelude.and» (ofBool (a == 2)) (ofBool (k == 2))).label = 0
  rw [and_ofBool]
  by_cases hak : a = 2 ∧ k = 2
  · obtain ⟨rfl, rfl⟩ := hak
    rw [Ty.prod?.eq_1] at hP
    cases hP
  · by_cases ha : a = 2
    · simp [ha, show k ≠ 2 from fun hk ↦ hak ⟨ha, hk⟩, ofBool]
    · simp [ha, ofBool]

/-- A tree the kernel reads as a list type passes the mirror's test, with the element type it
reads. -/
theorem list_some {L A : Tree} {h : Ty.den L = List (Ty.den A)}
    (hL : Ty.list? L = some ⟨A, h⟩) :
    («Check.isListTy» L).label ≠ 0 ∧ Const.child L (leaf 0) = A := by
  obtain ⟨⟨a, k⟩, g⟩ := L
  by_cases hak : a = 4 ∧ k = 1
  · obtain ⟨rfl, rfl⟩ := hak
    rw [Ty.list?.eq_1] at hL
    cases hL
    exact ⟨Nat.one_ne_zero, rfl⟩
  · rw [Ty.list?.eq_2 _ fun _ h ↦ hak (Prod.mk.inj (mk_index_eq h))] at hL
    cases hL

/-- A tree the kernel does not read as a list type fails the mirror's test. -/
theorem list_none {L : Tree} (hL : Ty.list? L = none) :
    («Check.isListTy» L).label = 0 := by
  obtain ⟨⟨a, k⟩, g⟩ := L
  change («Prelude.and» (ofBool (a == 4)) (ofBool (k == 1))).label = 0
  rw [and_ofBool]
  by_cases hak : a = 4 ∧ k = 1
  · obtain ⟨rfl, rfl⟩ := hak
    rw [Ty.list?.eq_1] at hL
    cases hL
  · by_cases ha : a = 4
    · simp [ha, show k ≠ 1 from fun hk ↦ hak ⟨ha, hk⟩, ofBool]
    · simp [ha, ofBool]

/-- The mirror's test of two optional trees' presence. -/
theorem both_enc (a b : Option Tree) :
    («Reader.both» (enc a) (enc b)).label ≠ 0 ↔ a.isSome ∧ b.isSome := by
  unfold «Reader.both»
  split <;> rename_i h <;> rw [isSome_enc] at h <;> simp_all [isSome_enc]

/-- The mirror's test of two optional trees' presence, as a truth value. -/
theorem both_enc_eq (a b : Option Tree) :
    «Reader.both» (enc a) (enc b) = ofBool (a.isSome && b.isSome) := by
  cases a <;> cases b <;> rfl

/-- The mirror's test of an optional tree's presence and a truth value. -/
theorem both_enc_ofBool (a : Option Tree) (b : Bool) :
    «Reader.both» (enc a) (ofBool b) = ofBool (a.isSome && b) := by
  cases a <;> cases b <;> rfl

/-- Equality of trees, as the kernel's primitive tests it. -/
theorem equal_label (a b : Tree) : (Const.equal a b).label ≠ 0 ↔ a = b := by
  simp [Const.equal, ofBool]

/-- The mirror's type of the fold of trees. -/
theorem foldTy_eq (A : Tree) : «Check.foldTy» A = foldTy A := by
  simp only [«Check.foldTy», tyArrow_eq, tyList_eq, Kernel.foldTy, tT, tList_eq]

/-- The mirror's type of iteration. -/
theorem iterTy_eq (A : Tree) : «Check.iterTy» A = iterTy A := by
  simp only [«Check.iterTy», tyArrow_eq, Kernel.iterTy, tT]

/-- The mirror's type of the right fold of lists. -/
theorem foldrTy_eq (A B : Tree) : «Check.foldrTy» A B = foldrTy A B := by
  simp only [«Check.foldrTy», tyArrow_eq, tyList_eq, Kernel.foldrTy]

/-- The mirror's type of case analysis of lists. -/
theorem lcaseTy_eq (A B : Tree) : «Check.lcaseTy» A B = lcaseTy A B := by
  simp only [«Check.lcaseTy», tyArrow_eq, tyList_eq, Kernel.lcaseTy]

/-- The mirror's type of a variable. -/
theorem node_var (G : List Glob) (Γ : Ctx) (n : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.var [n]) (withTys G [n]) Γ =
      enc (tyOf G Γ (RoseTree.node Label.var [n])) := by
  change «Prelude.nth» Γ (leaf n.label) = _
  rw [nth_eq, tyOf_node, List.map_singleton, inferStep_var]

/-- The mirror's type of an abstraction. -/
theorem node_lam (G : List Glob) (Γ : Ctx) (A b : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.lam [A, b]) (withTys G [A, b])
      Γ = enc (tyOf G Γ (RoseTree.node Label.lam [A, b])) := by
  change (if («Check.isTy» A).label ≠ 0 then
      (if («Prelude.isSome» (enc (tyOf G (A :: Γ) b))).label ≠ 0 then
        «Prelude.some» («Check.tyArrow» A
          («Prelude.get» (enc (tyOf G (A :: Γ) b))))
      else «Prelude.none») else «Prelude.none») = _
  rw [tyOf_node, List.map_cons, List.map_singleton, inferStep_lam, isTy_eq]
  change _ = enc (if Ty.IsTy A then (tyOf G (A :: Γ) b).map (tArrow A) else none)
  cases Ty.IsTy A <;> cases tyOf G (A :: Γ) b <;>
    simp [isSome_enc, get_enc, some_eq, none_eq, tyArrow_eq]

/-- The mirror's type of an application. -/
theorem node_app (G : List Glob) (Γ : Ctx) (f x : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.app [f, x]) (withTys G [f, x])
      Γ = enc (tyOf G Γ (RoseTree.node Label.app [f, x])) := by
  change (if («Reader.both» (enc (tyOf G Γ f)) (enc (tyOf G Γ x))).label ≠ 0 then
      (if («Check.isArrow» («Prelude.get» (enc (tyOf G Γ f)))).label ≠ 0 then
        (if (Const.equal («Prelude.get» (enc (tyOf G Γ x)))
            (Const.child («Prelude.get» (enc (tyOf G Γ f))) (leaf 0))).label ≠ 0 then
          «Prelude.some» (Const.child («Prelude.get» (enc (tyOf G Γ f))) (leaf 1))
        else «Prelude.none»)
      else «Prelude.none») else «Prelude.none») = _
  rw [tyOf_node, List.map_cons, List.map_singleton, inferStep_app]
  change _ = enc ((tyOf G Γ f).bind fun F ↦ (tyOf G Γ x).bind fun X ↦
    (Ty.arrow? F).bind fun p ↦ if X = p.1 then some p.2.1 else none)
  cases tyOf G Γ f with
  | none => simp [both_enc, none_eq]
  | some F =>
    cases tyOf G Γ x with
    | none => simp [both_enc, none_eq]
    | some X =>
      rcases hF : Ty.arrow? F with _ | ⟨A, B, h⟩
      · simp [both_enc, get_enc, arrow_none hF, none_eq, hF]
      · obtain ⟨harrow, h0, h1⟩ := arrow_some hF
        simp only [both_enc, get_enc, harrow, h0, h1, equal_label, some_eq, none_eq, hF,
          Option.isSome_some, and_self, ne_eq, not_false_eq_true, ite_true, Option.bind_some]
        split <;> rfl

/-- The mirror's type of the unit value. -/
theorem node_unit (G : List Glob) (Γ : Ctx) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.unit []) (withTys G []) Γ =
      enc (tyOf G Γ (RoseTree.node Label.unit [])) := rfl

/-- The mirror's type of a pair. -/
theorem node_pair (G : List Glob) (Γ : Ctx) (a b : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.pair [a, b])
      (withTys G [a, b]) Γ = enc (tyOf G Γ (RoseTree.node Label.pair [a, b])) := by
  change «Reader.some2» (leaf 2) (enc (tyOf G Γ a)) (enc (tyOf G Γ b)) = _
  rw [some2_eq, tyOf_node, List.map_cons, List.map_singleton, inferStep_pair]
  rfl

/-- The mirror's type of a first projection. -/
theorem node_fst (G : List Glob) (Γ : Ctx) (p : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.fst [p]) (withTys G [p]) Γ =
      enc (tyOf G Γ (RoseTree.node Label.fst [p])) := by
  change (if («Prelude.isSome» (enc (tyOf G Γ p))).label ≠ 0 then
      (if («Check.isProd» («Prelude.get» (enc (tyOf G Γ p)))).label ≠ 0 then
        «Prelude.some» (Const.child («Prelude.get» (enc (tyOf G Γ p))) (leaf 0))
      else «Prelude.none») else «Prelude.none») = _
  rw [tyOf_node, List.map_singleton, inferStep_fst]
  change _ = enc ((tyOf G Γ p).bind fun P ↦ (Ty.prod? P).map (·.1))
  cases tyOf G Γ p with
  | none => simp [isSome_enc, none_eq]
  | some P =>
    rcases hP : Ty.prod? P with _ | ⟨A, B, h⟩
    · simp [isSome_enc, get_enc, prod_none hP, none_eq, hP]
    · obtain ⟨hprod, h0, _⟩ := prod_some hP
      simp [isSome_enc, get_enc, hprod, h0, some_eq, hP]

/-- The mirror's type of a second projection. -/
theorem node_snd (G : List Glob) (Γ : Ctx) (p : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.snd [p]) (withTys G [p]) Γ =
      enc (tyOf G Γ (RoseTree.node Label.snd [p])) := by
  change (if («Prelude.isSome» (enc (tyOf G Γ p))).label ≠ 0 then
      (if («Check.isProd» («Prelude.get» (enc (tyOf G Γ p)))).label ≠ 0 then
        «Prelude.some» (Const.child («Prelude.get» (enc (tyOf G Γ p))) (leaf 1))
      else «Prelude.none») else «Prelude.none») = _
  rw [tyOf_node, List.map_singleton, inferStep_snd]
  change _ = enc ((tyOf G Γ p).bind fun P ↦ (Ty.prod? P).map (·.2.1))
  cases tyOf G Γ p with
  | none => simp [isSome_enc, none_eq]
  | some P =>
    rcases hP : Ty.prod? P with _ | ⟨A, B, h⟩
    · simp [isSome_enc, get_enc, prod_none hP, none_eq, hP]
    · obtain ⟨hprod, _, h1⟩ := prod_some hP
      simp [isSome_enc, get_enc, hprod, h1, some_eq, hP]

/-- The mirror's type of a quoted tree. -/
theorem node_quote (G : List Glob) (Γ : Ctx) (t : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.quote [t]) (withTys G [t]) Γ =
      enc (tyOf G Γ (RoseTree.node Label.quote [t])) := by
  rw [tyOf_node]
  rfl

/-- The mirror's type of a conditional. -/
theorem node_cond (G : List Glob) (Γ : Ctx) (c a b : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.cond [c, a, b])
      (withTys G [c, a, b]) Γ = enc (tyOf G Γ (RoseTree.node Label.cond [c, a, b])) := by
  change (if («Reader.both» (enc (tyOf G Γ c))
        («Reader.both» (enc (tyOf G Γ a)) (enc (tyOf G Γ b)))).label ≠ 0 then
      (if (Const.equal («Prelude.get» (enc (tyOf G Γ c))) (leaf 0)).label ≠ 0 then
        (if (Const.equal («Prelude.get» (enc (tyOf G Γ b)))
            («Prelude.get» (enc (tyOf G Γ a)))).label ≠ 0 then enc (tyOf G Γ a)
        else «Prelude.none»)
      else «Prelude.none») else «Prelude.none») = _
  rw [tyOf_node, List.map_cons, List.map_cons, List.map_singleton, inferStep_cond]
  change _ = enc ((tyOf G Γ c).bind fun C ↦ (tyOf G Γ a).bind fun A ↦ (tyOf G Γ b).bind fun B ↦
    if C = tT then if B = A then some A else none else none)
  rw [both_enc_eq, both_enc_ofBool]
  cases tyOf G Γ c <;> cases tyOf G Γ a <;> cases tyOf G Γ b <;>
    simp only [ofBool_label, Option.isSome_some, Option.isSome_none, Bool.and_true,
      Bool.and_false, Bool.false_eq_true, ite_false, ite_true, none_eq, Option.bind_some,
      Option.bind_none, get_enc, equal_label, tT]
  split_ifs <;> first | rfl | simp_all

/-- The mirror's type of the fold of trees. -/
theorem node_fold (G : List Glob) (Γ : Ctx) (A : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.fold [A]) (withTys G [A]) Γ =
      enc (tyOf G Γ (RoseTree.node Label.fold [A])) := by
  change (if («Check.isTy» A).label ≠ 0 then «Prelude.some»
    («Check.foldTy» A) else «Prelude.none») = _
  rw [tyOf_node]
  change _ = enc (fstOf (if Ty.IsTy A then some (constant ⟨foldTy A, foldDen A⟩) else none))
  rw [isTy_eq, foldTy_eq]
  cases Ty.IsTy A <;> rfl

/-- The mirror's type of the fold of trees whose step sees the node itself: the type of the
fold. -/
theorem node_para (G : List Glob) (Γ : Ctx) (A : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.para [A]) (withTys G [A]) Γ =
      enc (tyOf G Γ (RoseTree.node Label.para [A])) := by
  change (if («Check.isTy» A).label ≠ 0 then «Prelude.some»
    («Check.foldTy» A) else «Prelude.none») = _
  rw [tyOf_node]
  change _ = enc (fstOf (if Ty.IsTy A then some (constant ⟨foldTy A, paraDen A⟩) else none))
  rw [isTy_eq, foldTy_eq]
  cases Ty.IsTy A <;> rfl

/-- The mirror's type of iteration. -/
theorem node_iter (G : List Glob) (Γ : Ctx) (A : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.iter [A]) (withTys G [A]) Γ =
      enc (tyOf G Γ (RoseTree.node Label.iter [A])) := by
  change (if («Check.isTy» A).label ≠ 0 then «Prelude.some»
    («Check.iterTy» A) else «Prelude.none») = _
  rw [tyOf_node]
  change _ = enc (fstOf (if Ty.IsTy A then some (constant ⟨iterTy A, iterDen A⟩) else none))
  rw [isTy_eq, iterTy_eq]
  cases Ty.IsTy A <;> rfl

/-- The mirror's type of the empty list. -/
theorem node_nil (G : List Glob) (Γ : Ctx) (A : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.nil [A]) (withTys G [A]) Γ =
      enc (tyOf G Γ (RoseTree.node Label.nil [A])) := by
  change (if («Check.isTy» A).label ≠ 0 then «Prelude.some»
    («Check.tyList» A) else «Prelude.none») = _
  rw [tyOf_node]
  change _ = enc (fstOf (if Ty.IsTy A then
    some (⟨tList A, fun _ ↦ ([] : List (Ty.den A))⟩ : Meaning Γ) else none))
  rw [isTy_eq, tyList_eq]
  cases Ty.IsTy A <;> rfl

/-- The mirror's type of a list construction. -/
theorem node_cons (G : List Glob) (Γ : Ctx) (x xs : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.cons [x, xs])
      (withTys G [x, xs]) Γ = enc (tyOf G Γ (RoseTree.node Label.cons [x, xs])) := by
  change (if («Reader.both» (enc (tyOf G Γ x)) (enc (tyOf G Γ xs))).label ≠ 0 then
      (if («Check.isListTy» («Prelude.get» (enc (tyOf G Γ xs)))).label ≠ 0 then
        (if (Const.equal («Prelude.get» (enc (tyOf G Γ x)))
            (Const.child («Prelude.get» (enc (tyOf G Γ xs))) (leaf 0))).label ≠ 0 then
          «Prelude.some» («Check.tyList» («Prelude.get»
            (enc (tyOf G Γ x))))
        else «Prelude.none»)
      else «Prelude.none») else «Prelude.none») = _
  rw [tyOf_node, List.map_cons, List.map_singleton, inferStep_cons]
  change _ = enc ((tyOf G Γ x).bind fun X ↦ (tyOf G Γ xs).bind fun L ↦
    (Ty.list? L).bind fun p ↦ if X = p.1 then some (tList p.1) else none)
  cases tyOf G Γ x with
  | none => simp [both_enc, none_eq]
  | some X =>
    cases tyOf G Γ xs with
    | none => simp [both_enc, none_eq]
    | some L =>
      rcases hL : Ty.list? L with _ | ⟨A, h⟩
      · simp [both_enc, get_enc, list_none hL, none_eq, hL]
      · obtain ⟨hlist, h0⟩ := list_some hL
        simp only [both_enc, get_enc, hlist, h0, equal_label, some_eq, none_eq, hL,
          Option.isSome_some, and_self, ne_eq, not_false_eq_true, ite_true, Option.bind_some,
          tyList_eq]
        split <;> simp_all

/-- The mirror's type of the right fold of lists. -/
theorem node_foldr (G : List Glob) (Γ : Ctx) (A B : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.foldr [A, B])
      (withTys G [A, B]) Γ = enc (tyOf G Γ (RoseTree.node Label.foldr [A, B])) := by
  change (if («Prelude.and» («Check.isTy» A)
      («Check.isTy» B)).label ≠ 0 then
    «Prelude.some» («Check.foldrTy» A B) else «Prelude.none») = _
  rw [tyOf_node]
  change _ = enc (fstOf (if (Ty.IsTy A && Ty.IsTy B) then
    some (constant ⟨foldrTy A B, foldrDen A B⟩) else none))
  rw [isTy_eq, isTy_eq, and_ofBool, foldrTy_eq]
  cases Ty.IsTy A && Ty.IsTy B <;> rfl

/-- The mirror's type of case analysis of lists. -/
theorem node_lcase (G : List Glob) (Γ : Ctx) (A B : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.lcase [A, B])
      (withTys G [A, B]) Γ = enc (tyOf G Γ (RoseTree.node Label.lcase [A, B])) := by
  change (if («Prelude.and» («Check.isTy» A)
      («Check.isTy» B)).label ≠ 0 then
    «Prelude.some» («Check.lcaseTy» A B) else «Prelude.none») = _
  rw [tyOf_node]
  change _ = enc (fstOf (if (Ty.IsTy A && Ty.IsTy B) then
    some (constant ⟨lcaseTy A B, lcaseDen A B⟩) else none))
  rw [isTy_eq, isTy_eq, and_ofBool, lcaseTy_eq]
  cases Ty.IsTy A && Ty.IsTy B <;> rfl

/-- The mirror's type of a primitive. -/
theorem node_prim (G : List Glob) (Γ : Ctx) (k : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.prim [k]) (withTys G [k]) Γ =
      enc (tyOf G Γ (RoseTree.node Label.prim [k])) := by
  change «Prelude.nth» «Check.primTypes» (leaf k.label) = _
  rw [nth_eq, primTypes_eq, tyOf_node, List.map_singleton, inferStep_prim]

/-- The mirror's type of a reference. -/
theorem node_ref (G : List Glob) (Γ : Ctx) (n : Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node Label.ref [n]) (withTys G [n]) Γ =
      enc (tyOf G Γ (RoseTree.node Label.ref [n])) := by
  change «Prelude.nth» (G.map (·.1)) (leaf n.label) = _
  rw [nth_eq, tyOf_node, List.map_singleton, inferStep_ref]

/-- The mirror's type of a node whose label is past the kernel's labels: nothing. -/
theorem node_other (G : List Glob) (Γ : Ctx) (l : ℕ) (hl : 25 < l) (cs : List Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node l cs) (withTys G cs) Γ =
      enc (tyOf G Γ (RoseTree.node l cs)) := by
  rw [tyOf_node]
  have hnone : inferStep l (cs.map fun c ↦ (c, RoseTree.para inferStep c)) G Γ = none := by
    unfold inferStep
    split <;> first | omega | rfl
  rw [hnone]
  unfold «Check.checkNode»
  simp only [label_node, children_node, arity_node, eq_leaf_ofBool, ofBool_label, beq_iff_eq,
    show l ≠ 8 by omega, show l ≠ 9 by omega, show l ≠ 10 by omega, show l ≠ 11 by omega,
    show l ≠ 12 by omega, show l ≠ 13 by omega, show l ≠ 14 by omega, show l ≠ 15 by omega,
    show l ≠ 16 by omega, show l ≠ 17 by omega, show l ≠ 18 by omega, show l ≠ 19 by omega,
    show l ≠ 20 by omega, show l ≠ 21 by omega, show l ≠ 22 by omega, show l ≠ 23 by omega,
    show l ≠ 24 by omega, show l ≠ 25 by omega, ite_false]
  rfl

/-- A node of four or more children fails every test of the kernel's arities. -/
theorem eq_arity_many (n k : ℕ) (hk : k ≤ 3) : Const.eq (leaf (n + 1 + 1 + 1 + 1)) (leaf k) =
    leaf 0 := by
  have : (n + 1 + 1 + 1 + 1 == k) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  rw [eq_leaf_ofBool, this]
  rfl

/-- The mirror's type of a node of four or more children: nothing. -/
theorem node_many (G : List Glob) (Γ : Ctx) (l : ℕ) (a b c d : Tree) (rest : List Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node l (a :: b :: c :: d :: rest))
      (withTys G (a :: b :: c :: d :: rest)) Γ =
      enc (tyOf G Γ (RoseTree.node l (a :: b :: c :: d :: rest))) := by
  by_cases hl : 25 < l
  · exact node_other G Γ l hl _
  rw [tyOf_node, List.map_cons, List.map_cons, List.map_cons, List.map_cons]
  unfold «Check.checkNode»
  simp only [arity_node, List.length_cons, eq_arity_many _ 0 (by omega),
    eq_arity_many _ 1 (by omega), eq_arity_many _ 2 (by omega), eq_arity_many _ 3 (by omega)]
  match l, hl with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ |
    12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ |
    23, _ | 24, _ | 25, _ => rfl
  | _ + 26, h => exact (h (by omega)).elim

/-- The mirror's type of a node, from its children's types. -/
theorem checkNode_eq (G : List Glob) (Γ : Ctx) (l : ℕ) (cs : List Tree) :
    «Check.checkNode» (G.map (·.1)) (RoseTree.node l cs) (withTys G cs) Γ =
      enc (tyOf G Γ (RoseTree.node l cs)) := by
  by_cases hl : 25 < l
  · exact node_other G Γ l hl cs
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · match l, hl with
    | 11, _ => exact node_unit G Γ
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 12, _ |
      13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ |
      24, _ | 25, _ => rfl
    | _ + 26, h => exact (h (by omega)).elim
  · match l, hl with
    | 8, _ => exact node_var G Γ a
    | 13, _ => exact node_fst G Γ a
    | 14, _ => exact node_snd G Γ a
    | 15, _ => exact node_quote G Γ a
    | 17, _ => exact node_fold G Γ a
    | 18, _ => exact node_iter G Γ a
    | 19, _ => exact node_nil G Γ a
    | 22, _ => exact node_prim G Γ a
    | 23, _ => exact node_ref G Γ a
    | 25, _ => exact node_para G Γ a
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 9, _ | 10, _ | 11, _ | 12, _ |
      16, _ | 20, _ | 21, _ | 24, _ => rfl
    | _ + 26, h => exact (h (by omega)).elim
  · match l, hl with
    | 9, _ => exact node_lam G Γ a b
    | 10, _ => exact node_app G Γ a b
    | 12, _ => exact node_pair G Γ a b
    | 20, _ => exact node_cons G Γ a b
    | 21, _ => exact node_foldr G Γ a b
    | 24, _ => exact node_lcase G Γ a b
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 11, _ | 13, _ | 14, _ |
      15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 22, _ | 23, _ | 25, _ => rfl
    | _ + 26, h => exact (h (by omega)).elim
  · match l, hl with
    | 16, _ => exact node_cond G Γ a b c
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ |
      12, _ | 13, _ | 14, _ | 15, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ |
      24, _ | 25, _ => rfl
    | _ + 26, h => exact (h (by omega)).elim
  · exact node_many G Γ l a b c d rest

/-- The step of the mirror's type checker at a node: the node rebuilt, and its type as a
function of the context. -/
def typeStep (Gt : List Tree) (l : Tree) (rs : List (Tree × (List Tree → Tree))) :
    Tree × (List Tree → Tree) :=
  (Const.node l («Reader.rrTrees» rs),
    fun Γ ↦ «Check.checkNode» Gt (Const.node l («Reader.rrTrees» rs)) rs Γ)

/-- The mirror's type checker's fold gives each tree with its type. -/
theorem fold_typeStep (G : List Glob) :
    ∀ t : Tree, Const.fold (typeStep (G.map (·.1))) t = (t, fun Γ ↦ enc (tyOf G Γ t)) :=
  RoseTree.ind fun l cs ih ↦ by
    rw [fold_node, List.map_congr_left ih]
    change typeStep _ (leaf l) (withTys G cs) = _
    have hcs : «Reader.rrTrees» (withTys G cs) = cs := by
      rw [rrTrees_eq, withTys, List.map_map]
      exact List.map_id cs
    unfold typeStep
    rw [hcs]
    exact Prod.ext rfl (funext fun Γ ↦ checkNode_eq G Γ l cs)

/-- The type checker written in Geb decides as the kernel's checker-evaluator: the type it gives
a term in a context, as an optional tree, is the type of the term's meaning. -/
theorem typeIn_eq (G : List Glob) (Γ : Ctx) (t : Tree) :
    «Check.typeIn» (G.map (·.1)) Γ t = enc (tyOf G Γ t) := by
  change (Const.fold (typeStep (G.map (·.1))) t).2 Γ = _
  rw [fold_typeStep]

/-! The inversion of the checker-evaluator at applications and abstractions. -/

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

/-- Function types with equal parts, and only they, are equal. -/
theorem tArrow_inj {A B A' B' : Tree} (h : tArrow A B = tArrow A' B') : A = A' ∧ B = B' := by
  have := congrArg RoseTree.children h
  simp only [tArrow, node2_eq, RoseTree.children_node, List.cons.injEq, and_true] at this
  exact this

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

end GebTests.Prototypes.CheckMirror
end
