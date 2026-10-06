/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.CheckMirror
public import Geb.Prototypes.Kernel.Eval

set_option doc.verso true in
/-!
# The evaluator written in Geb evaluates as Lean's

The evaluator of kernel terms written in Geb, {lit}`bootstrap/eval.geb`, in the Lean the
bootstrap compiler emits from the kernel's program ({lit}`GebMirror.Kernel`), equals the
evaluator {name}`Geb.Kernel.Eval.eval` at every level of fuel, environment and term, an optional
value as the reader represents an optional tree ({lit}`enc`), and an optional list as the
optional node of label zero over it. Each of the mirror's definitions is related to the Lean
definition it transcribes: the mirror's tests of labels and numbers of children select the case
the Lean definition's pattern selects. The levels of fuel agree by induction on the fuel, and at
each level the evaluation agrees by induction on the term.

## Main definitions

* {lit}`FnsRel` — the relation of the mirror's functions at a level to the Lean ones.

## Main statements

* {lit}`level_rel` — the mirror's levels are related to the Lean ones.
* {lit}`eval_eq`, {lit}`apply_eq` — the mirror's evaluation and application are the Lean ones.

## Tags

evaluation, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Kernel

namespace GebTests.Prototypes.EvalMirror

open Geb Geb.Kernel Geb.Kernel.Eval GebTests.Prototypes.CheckMirror
open scoped FinEnum

/-! Options and lists. -/

/-- The mirror's binding of a present optional tree. -/
@[simp] theorem bindO_some (x : Tree) (f : Tree → Tree) : «Eval.bindO» (enc (some x)) f = f x := by
  simp [«Eval.bindO», isSome_enc, get_enc]

/-- The mirror's binding of an absent optional tree. -/
@[simp] theorem bindO_none (f : Tree → Tree) : «Eval.bindO» (enc none) f = enc none := rfl

/-- The mirror's binding of an encoded optional tree, at a continuation related to one of
trees. -/
theorem bindO_enc (o : Option Tree) {f : Tree → Tree} {g : Tree → Option Tree}
    (h : ∀ x, f x = enc (g x)) : «Eval.bindO» (enc o) f = enc (o.bind g) := by
  rcases o with _ | x
  · rfl
  · simp [h]

/-- The mirror's image of a list. -/
theorem mapT_eq (f : Tree → Tree) (xs : List Tree) : «Eval.mapT» f xs = xs.map f :=
  List.rec rfl (fun x xs ih ↦ by
    change f x :: «Eval.mapT» f xs = _
    rw [ih]
    rfl) xs

/-- The mirror's values of a list of encoded optional trees, when every one is present. -/
theorem allSomeT_eq (os : List (Option Tree)) :
    «Eval.allSomeT» (os.map enc) = enc ((os.mapM id).map (RoseTree.node 0)) := by
  refine List.rec rfl (fun o os ih ↦ ?_) os
  change (if («Prelude.isSome» (enc o)).label ≠ 0 then
      «Eval.bindO» («Eval.allSomeT» (os.map enc)) (fun x3 ↦
        «Prelude.some» (Const.node (leaf 0) («Prelude.get» (enc o) :: Const.children x3)))
    else «Prelude.none») = _
  rw [ih]
  rcases o with _ | a
  · simp [isSome_enc, List.mapM_cons, none_eq]
  · rcases hm : os.mapM id with _ | xs
    · simp [isSome_enc, hm, List.mapM_cons]
    · simp only [isSome_enc, Option.isSome_some, ne_eq, ↓reduceIte, hm,
        Option.map_some, bindO_some, get_enc, CheckMirror.children_node, some_eq, List.mapM_cons,
        id, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl

/-! Values. -/

/-- The mirror's values are the Lean ones. -/
theorem valQuote_eq (t : Tree) : «Eval.valQuote» t = Val.quote t := rfl

theorem valUnit_eq : «Eval.valUnit» = Val.unit := rfl

theorem valPair_eq (a b : Tree) : «Eval.valPair» a b = Val.pair a b := rfl

theorem valClo_eq (env : List Tree) (A b : Tree) : «Eval.valClo» env A b = Val.clo env A b :=
  rfl

theorem valApp_eq (f x : Tree) : «Eval.valApp» f x = Val.app f x := rfl

theorem ofList_eq (A : Tree) (vs : List Tree) : «Eval.ofList» A vs = Val.ofList A vs := rfl

/-! Reading values. -/

/-- The mirror's disjunction of truth values. -/
theorem or_ofBool (a b : Bool) : «Prelude.or» (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-- The comparison of two labels' order, as a truth value. -/
theorem lt_leaf_ofBool (a b : ℕ) : Const.lt (leaf a) (leaf b) = ofBool (decide (a < b)) := rfl

/-- The tests of a node's label and number of children. -/
theorem node_tests (l : ℕ) (cs : List Tree) (a n : ℕ) :
    «Prelude.and» (Const.eq (Const.label (RoseTree.node l cs)) (leaf a))
      (Const.eq (Const.arity (RoseTree.node l cs)) (leaf n)) =
      ofBool (l == a && cs.length == n) := by
  rw [label_node, arity_node, eq_leaf_ofBool, eq_leaf_ofBool, and_ofBool]

/-- The mirror's tree of a quotation. -/
theorem unquote_eq (v : Tree) : «Eval.unquote» v = enc (unquote v) := by
  rw [← RoseTree.node_label_children v]
  generalize v.label = l
  generalize v.children = cs
  unfold «Eval.unquote»
  rw [node_tests]
  by_cases hl : l = Label.quote
  · subst hl
    rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩
    · rfl
    · simp [some_eq, child_node, unquote]
    · simp [unquote, none_eq]
  · simp [hl, unquote, none_eq]

/-- The mirror's elements of a list value. -/
theorem listOf_eq : ∀ v : Tree, «Eval.listOf» v = enc ((listOf v).map (RoseTree.node 0)) := by
  refine RoseTree.ind fun l cs ih ↦ ?_
  have hm : «Eval.listOf» (RoseTree.node l cs) =
      (if (ofBool (l == Label.nil && cs.length == 1)).label ≠ 0 then
        «Prelude.some» (Const.node (leaf 0) [])
      else if (ofBool (l == Label.cons && cs.length == 2)).label ≠ 0 then
        «Eval.bindO» («Prelude.at» (cs.map «Eval.listOf») (leaf 1)) (fun x3 ↦
          «Prelude.some» (Const.node (leaf 0)
            (Const.child (RoseTree.node l cs) (leaf 0) :: Const.children x3)))
      else «Prelude.none») := by
    unfold «Eval.listOf»
    rw [Const.para_node, node_tests, node_tests]
  rw [hm]
  simp only [listOf, RoseTree.para_node]
  rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, cs⟩⟩⟩
  · simp [none_eq]
  · by_cases hl : l = Label.nil
    · subst hl
      simp [some_eq]
      rfl
    · simp [hl, none_eq]
  · by_cases hl : l = Label.cons
    · subst hl
      have hy := ih y (by simp)
      simp only [List.map_cons, List.map_nil, at_eq, List.getD_cons_succ, List.getD_cons_zero,
        hy, child_node, List.length_cons, List.length_nil]
      simp only [listOf] at hy ⊢
      rcases RoseTree.para _ y with _ | ys
      · simp
      · simp [some_eq, CheckMirror.children_node]
        rfl
    · simp [hl, none_eq]
  · simp [none_eq]

/-- The mirror's concatenation of lists. -/
theorem append_eq (xs ys : List Tree) : «Prelude.append» xs ys = xs ++ ys :=
  List.rec rfl (fun x xs ih ↦ by
    change x :: «Prelude.append» xs ys = _
    rw [ih]
    rfl) xs

/-- The mirror's head and arguments of a partial application. -/
theorem spine_eq : ∀ v : Tree, «Eval.spine» v = spine v := by
  refine RoseTree.ind fun l cs ih ↦ ?_
  have hm : «Eval.spine» (RoseTree.node l cs) =
      (if (ofBool (l == Label.app && cs.length == 2)).label ≠ 0 then
        Const.lcase (cs.map «Eval.spine») (RoseTree.node l cs, []) (fun x3 _ ↦
          (x3.1, «Prelude.append» x3.2
            («Prelude.single» (Const.child (RoseTree.node l cs) (leaf 1)))))
      else (RoseTree.node l cs, [])) := by
    unfold «Eval.spine»
    rw [Const.para_node, node_tests]
  rw [hm]
  simp only [spine, RoseTree.para_node]
  rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, cs⟩⟩⟩
  · simp
  · simp
  · by_cases hl : l = Label.app
    · subst hl
      simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil,
        ofBool_label, ne_eq, Const.lcase, append_eq,
        child_node, List.getD_cons_succ, List.getD_cons_zero, ih x (by simp)]
      rfl
    · simp [hl]
  · simp [List.map_map, Function.comp_def]

/-- The mirror's number of arguments of a primitive. -/
theorem primArity_eq (k : ℕ) : «Eval.primArity» (leaf k) = leaf (primArity k) := by
  unfold «Eval.primArity» primArity
  simp only [eq_leaf_ofBool, or_ofBool, lt_leaf_ofBool, ofBool_label, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq]
  split <;> (try split) <;> rfl

/-- The mirror's number of arguments of a constant. -/
theorem constArity_eq (h : Tree) : «Eval.constArity» h = leaf (arity h) := by
  rw [← RoseTree.node_label_children h]
  generalize h.label = l
  generalize h.children = cs
  unfold «Eval.constArity» arity
  simp only [label_node, arity_node, eq_leaf_ofBool, or_ofBool, and_ofBool, ofBool_label,
    RoseTree.label_node, RoseTree.children_node]
  rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, cs⟩⟩⟩
  · simp
  · simp only [List.length_cons, List.length_nil, child_node, List.getD_cons_zero]
    match l with
    | 17 | 25 => rfl
    | 18 => rfl
    | 22 => exact primArity_eq _
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 19 | 20 | 21
      | 23 | 24 | _ + 26 => simp
  · match l with
    | 21 | 24 => rfl
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19
      | 20 | 22 | 23 | _ + 25 => simp
  · simp

/-- The mirror's trees a list of values quotes, when every one is a quotation. -/
theorem unquotes_eq (args : List Tree) :
    «Eval.allSomeT» («Eval.mapT» «Eval.unquote» args) =
      enc ((args.mapM unquote).map (RoseTree.node 0)) := by
  rw [mapT_eq, show args.map «Eval.unquote» = (args.map unquote).map enc by
    simp [List.map_map, Function.comp_def, unquote_eq], allSomeT_eq]
  congr 2
  exact List.rec rfl (fun a as ih ↦ by simp [List.mapM_cons, ih]) args

set_option maxHeartbeats 1000000 in
-- the case analysis of the primitives' indices compares two chains of conditionals
/-- The mirror's primitive applied to the trees its arguments quote. -/
theorem primApply_eq (k : ℕ) (args : List Tree) :
    «Eval.primApply» (leaf k) args = enc (primApply k args) := by
  unfold «Eval.primApply» primApply
  rw [unquotes_eq]
  rcases args.mapM unquote with _ | ts
  · rfl
  · simp only [Option.map_some, bindO_some, CheckMirror.children_node, length_eq, at_eq,
      Option.bind_eq_bind, Option.bind_some]
    rcases ts with _ | ⟨a, _ | ⟨b, _ | ⟨c, ts⟩⟩⟩
    · simp [eq_leaf_ofBool, none_eq]
    · simp only [List.length_cons, List.length_nil, eq_leaf_ofBool, ofBool_label, beq_iff_eq,
        List.getD_cons_zero, valQuote_eq, ofList_eq, mapT_eq, Prim.label, Prim.arity,
        Prim.children, Prim.log2]
      split_ifs <;> rfl
    · simp only [List.length_cons, List.length_nil, eq_leaf_ofBool, ofBool_label, beq_iff_eq,
        List.getD_cons_zero, List.getD_cons_succ, valQuote_eq, Prim.child, Prim.add, Prim.sub,
        Prim.mul, Prim.div, Prim.mod, Prim.eq, Prim.lt, Prim.equal]
      split_ifs <;> first | (exfalso; omega) | rfl
    · have h₁ : ¬(Const.eq (leaf (a :: b :: c :: ts).length) (leaf 1)).label ≠ 0 := by
        rw [eq_leaf]
        simp only [List.length_cons]
        omega
      have h₂ : ¬(Const.eq (leaf (a :: b :: c :: ts).length) (leaf 2)).label ≠ 0 := by
        rw [eq_leaf]
        simp only [List.length_cons]
        omega
      simp only [h₁, h₂, ↓reduceIte]
      rfl

/-- The mirror's node primitive applied to a label's value and a list value of children. -/
theorem primNode_eq (l cs : Tree) : «Eval.primNode» l cs = enc (primNode l cs) := by
  unfold «Eval.primNode» primNode
  rw [unquote_eq]
  refine bindO_enc _ fun a ↦ ?_
  rw [listOf_eq]
  rcases listOf cs with _ | vs
  · rfl
  · simp only [Option.map_some, bindO_some, CheckMirror.children_node, Option.bind_eq_bind,
      Option.bind_some]
    rw [unquotes_eq]
    rcases hts : vs.mapM unquote with _ | ts
    · rfl
    · simp [some_eq, valQuote_eq, CheckMirror.children_node]

/-! The constants. -/

/-- The mirror's binding of the encoding of an optional list as the node of label zero over it,
at a continuation related to one of lists. -/
theorem bindO_list (o : Option (List Tree)) {f : Tree → Tree} {g : List Tree → Option Tree}
    (h : ∀ xs, f (RoseTree.node 0 xs) = enc (g xs)) :
    «Eval.bindO» (enc (o.map (RoseTree.node 0))) f = enc (o.bind g) := by
  rcases o with _ | xs
  · rfl
  · simp [h]

/-- The mirror's application of values is related to an application when it gives, at every pair
of values, the encoding of its result. -/
def ApRel (ap' : Tree → Tree → Tree) (ap : Tree → Tree → Option Tree) : Prop :=
  ∀ f x, ap' f x = enc (ap f x)

/-- The mirror's last steps of a fold: the step applied to a node's value and to the list value of
its children's results. -/
theorem foldStep_eq {ap' : Tree → Tree → Tree} {ap : Tree → Tree → Option Tree} (h : ApRel ap' ap)
    (A f n : Tree) (xs : List Tree) :
    «Eval.bindO» (ap' f («Eval.valQuote» n)) (fun g ↦
        ap' g («Eval.ofList» A (Const.children (RoseTree.node 0 xs)))) =
      enc ((ap f (Val.quote n)).bind fun g ↦ ap g (Val.ofList A xs)) := by
  rw [h, valQuote_eq]
  exact bindO_enc _ fun g ↦ by rw [h, ofList_eq, CheckMirror.children_node]

/-- The mirror's fold at a related application. -/
theorem foldVal_eq {ap' : Tree → Tree → Tree} {ap : Tree → Tree → Option Tree} (h : ApRel ap' ap)
    (A f : Tree) : ∀ t, «Eval.foldVal» ap' A f t = enc (foldVal ap A f t) := by
  refine RoseTree.ind fun l cs ih ↦ ?_
  unfold «Eval.foldVal»
  rw [fold_node]
  change «Eval.bindO» («Eval.allSomeT» (cs.map («Eval.foldVal» ap' A f))) _ = _
  rw [List.map_congr_left ih, show (cs.map fun a ↦ enc (foldVal ap A f a)) =
    (cs.map (foldVal ap A f)).map enc by simp, allSomeT_eq]
  simp only [foldVal, RoseTree.elim_node]
  exact bindO_list _ fun xs ↦ foldStep_eq h A f _ xs

/-- The mirror's fold whose step sees the node, at a related application. -/
theorem paraVal_eq {ap' : Tree → Tree → Tree} {ap : Tree → Tree → Option Tree} (h : ApRel ap' ap)
    (A f : Tree) : ∀ t, «Eval.paraVal» ap' A f t = enc (paraVal ap A f t) := by
  refine RoseTree.ind fun l cs ih ↦ ?_
  unfold «Eval.paraVal»
  rw [Const.para_node]
  change «Eval.bindO» («Eval.allSomeT» (cs.map («Eval.paraVal» ap' A f))) _ = _
  rw [List.map_congr_left ih, show (cs.map fun a ↦ enc (paraVal ap A f a)) =
    (cs.map (paraVal ap A f)).map enc by simp, allSomeT_eq]
  simp only [paraVal, RoseTree.para_node, List.map_map, Function.comp_def, List.map_id']
  exact bindO_list _ fun xs ↦ foldStep_eq h A f _ xs

/-- The mirror's iteration at a related application. -/
theorem iterVal_eq {ap' : Tree → Tree → Tree} {ap : Tree → Tree → Option Tree} (h : ApRel ap' ap)
    (s z : Tree) : ∀ n : ℕ, «Eval.iterVal» ap' s z (leaf n) = enc (iterVal ap s z n) :=
  Nat.rec rfl fun n ih ↦ by
    change «Eval.bindO» («Eval.iterVal» ap' s z (leaf n)) (ap' s) = _
    rw [ih]
    exact bindO_enc _ fun x ↦ h s x

/-- The mirror's right fold at a related application. -/
theorem foldrVal_eq {ap' : Tree → Tree → Tree} {ap : Tree → Tree → Option Tree} (h : ApRel ap' ap)
    (g z : Tree) : ∀ vs, «Eval.foldrVal» ap' g z vs = enc (foldrVal ap g z vs) :=
  List.rec rfl fun x vs ih ↦ by
    change «Eval.bindO» («Eval.foldrVal» ap' g z vs)
      (fun a ↦ «Eval.bindO» (ap' g x) fun g1 ↦ ap' g1 a) = _
    rw [ih]
    exact bindO_enc _ fun a ↦ by rw [h]; exact bindO_enc _ fun g1 ↦ h g1 a

/-- The mirror's case analysis of a list value at a related application. -/
theorem lcaseVal_eq {ap' : Tree → Tree → Tree} {ap : Tree → Tree → Option Tree} (h : ApRel ap' ap)
    (xs n c : Tree) : «Eval.lcaseVal» ap' xs n c = enc (lcaseVal ap xs n c) := by
  rw [← RoseTree.node_label_children xs]
  generalize xs.label = l
  generalize xs.children = cs
  unfold «Eval.lcaseVal» lcaseVal
  rw [node_tests, node_tests]
  simp only [RoseTree.label_node, RoseTree.children_node]
  rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, cs⟩⟩⟩
  · simp [none_eq]
  · by_cases hl : l = Label.nil
    · subst hl
      rfl
    · simp [hl, none_eq]
  · by_cases hl : l = Label.cons
    · subst hl
      simp +decide only [List.length_cons, List.length_nil,
        ne_eq, ↓reduceIte, child_node, List.getD_cons_zero, List.getD_cons_succ]
      rw [h]
      exact bindO_enc _ fun g ↦ h g y
    · simp [hl, none_eq]
  · simp [none_eq]

/-- The label of a tree, as the kernel's primitive gives it. -/
theorem const_label (t : Tree) : Const.label t = leaf t.label := rfl

set_option maxHeartbeats 1000000 in
-- the constants' cases compare two chains of conditionals
/-- The mirror's constant applied to all its arguments, at a related application. -/
theorem sat_eq {ap' : Tree → Tree → Tree} {ap : Tree → Tree → Option Tree} (h : ApRel ap' ap)
    (hd : Tree) (args : List Tree) : «Eval.sat» ap' hd args = enc (sat ap hd args) := by
  rw [← RoseTree.node_label_children hd]
  generalize hd.label = l
  generalize hd.children = cs
  unfold «Eval.sat» sat
  simp only [arity_node, length_eq, at_eq, child_node, eq_leaf_ofBool, and_ofBool,
    ofBool_label, Bool.and_eq_true, beq_iff_eq, RoseTree.label_node, RoseTree.children_node,
    Label.fold, Label.para, Label.iter, Label.foldr, Label.lcase, Label.prim, Prim.node,
    const_label]
  split_ifs
  · exact bindO_enc _ (foldVal_eq h _ _) ▸ by rw [unquote_eq]
  · exact bindO_enc _ (paraVal_eq h _ _) ▸ by rw [unquote_eq]
  · rw [unquote_eq]
    exact bindO_enc _ fun n₀ ↦ iterVal_eq h _ _ n₀.label
  · rw [listOf_eq]
    exact bindO_list _ fun xs ↦ by rw [CheckMirror.children_node]; exact foldrVal_eq h _ _ xs
  · exact lcaseVal_eq h _ _ _
  · exact primNode_eq _ _
  · exact primApply_eq _ _
  · exact primApply_eq _ _
  · rfl

/-! Evaluation and application. -/

/-- The mirror's functions at a level are related to the Lean ones when the evaluation gives the
encoding of the Lean evaluation and the application is related to the Lean application. -/
def FnsRel (P : (List Tree → Tree → Tree) × (Tree → Tree → Tree)) (p : Fns) : Prop :=
  (∀ env t, P.1 env t = enc (p.1 env t)) ∧ ApRel P.2 p.2

/-- The mirror's first projection of a pair value. -/
theorem fst_eq (vp : Tree) :
    «Eval.pairFst» vp =
      enc (match vp.label, vp.children with
        | Label.pair, [a, _] => some a
        | _, _ => none) := by
  unfold «Eval.pairFst»
  rw [← RoseTree.node_label_children vp]
  generalize vp.label = l
  generalize vp.children = cs
  rw [node_tests]
  simp only [RoseTree.label_node, RoseTree.children_node]
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · simp [none_eq]
  · simp [none_eq]
  · by_cases hl : l = Label.pair
    · subst hl
      simp [some_eq, child_node]
    · simp [hl, none_eq]
  · simp [none_eq]

/-- The mirror's second projection of a pair value. -/
theorem snd_eq (vp : Tree) :
    «Eval.pairSnd» vp =
      enc (match vp.label, vp.children with
        | Label.pair, [_, b] => some b
        | _, _ => none) := by
  unfold «Eval.pairSnd»
  rw [← RoseTree.node_label_children vp]
  generalize vp.label = l
  generalize vp.children = cs
  rw [node_tests]
  simp only [RoseTree.label_node, RoseTree.children_node]
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · simp [none_eq]
  · simp [none_eq]
  · by_cases hl : l = Label.pair
    · subst hl
      simp [some_eq, child_node]
    · simp [hl, none_eq]
  · simp [none_eq]

/-- The mirror's evaluation step at a node without children. -/
theorem evStep_nil (G : List Tree) (P : (List Tree → Tree → Tree) × (Tree → Tree → Tree))
    (p : Fns) (l : ℕ) (env : List Tree) :
    «Eval.evStep» G P (RoseTree.node l []) [] env = enc (evStep G p l [] env) := by
  unfold «Eval.evStep»
  simp only [label_node, arity_node, eq_leaf_ofBool, or_ofBool, and_ofBool,
    ofBool_label, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.length_nil, Const.lcase]
  match l with
  | 11 => rfl
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20
    | 21 | 22 | 23 | 24 | 25 | _ + 26 => simp [evStep, none_eq]


/-- The mirror's evaluation step at a node of one child. -/
theorem evStep_one (G : List Tree) {P : (List Tree → Tree → Tree) × (Tree → Tree → Tree)}
    {p : Fns} (hP : FnsRel P p) (l : ℕ) (x : Tree) (f' : List Tree → Tree)
    (f : List Tree → Option Tree) (hf : ∀ env, f' env = enc (f env)) (env : List Tree) :
    «Eval.evStep» G P (RoseTree.node l [x]) [f'] env = enc (evStep G p l [(x, f)] env) := by
  unfold «Eval.evStep»
  simp only [arity_node, eq_leaf_ofBool, or_ofBool, and_ofBool, ofBool_label,
    Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.length_cons, List.length_nil,
    Const.lcase, child_node, List.getD_cons_zero, const_label]
  match l with
  | 8 => simp [evStep, nth_eq]
  | 13 =>
    simp only [evStep]
    rw [hf]
    exact bindO_enc _ fst_eq
  | 14 =>
    simp only [evStep]
    rw [hf]
    exact bindO_enc _ snd_eq
  | 15 | 17 | 18 | 19 | 22 | 25 => rfl
  | 23 =>
    simp only [evStep, nth_eq]
    exact bindO_enc _ fun t ↦ hP.1 [] t
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 | 10 | 11 | 12 | 16 | 20 | 21 | 24 | _ + 26 =>
    simp [evStep, none_eq]

/-- The mirror's evaluation step at a node of two children. -/
theorem evStep_two (G : List Tree) {P : (List Tree → Tree → Tree) × (Tree → Tree → Tree)}
    {p : Fns} (hP : FnsRel P p) (l : ℕ) (x y : Tree) (f' g' : List Tree → Tree)
    (f g : List Tree → Option Tree) (hf : ∀ env, f' env = enc (f env))
    (hg : ∀ env, g' env = enc (g env)) (env : List Tree) :
    «Eval.evStep» G P (RoseTree.node l [x, y]) [f', g'] env =
      enc (evStep G p l [(x, f), (y, g)] env) := by
  unfold «Eval.evStep»
  simp only [label_node, arity_node, eq_leaf_ofBool, or_ofBool, and_ofBool, ofBool_label,
    Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.length_cons, List.length_nil,
    Nat.reduceAdd, Const.lcase, child_node, List.getD_cons_zero, List.getD_cons_succ]
  match l with
  | 9 => rfl
  | 10 =>
    simp +decide only [evStep, ↓reduceIte]
    rw [hf]
    refine bindO_enc _ fun vf ↦ ?_
    rw [hg]
    exact bindO_enc _ fun vx ↦ hP.2 vf vx
  | 12 =>
    simp +decide only [evStep, ↓reduceIte]
    rw [hf]
    refine bindO_enc _ fun va ↦ ?_
    rw [hg]
    exact bindO_enc _ fun vb ↦ rfl
  | 20 =>
    simp +decide only [evStep, ↓reduceIte]
    rw [hf]
    refine bindO_enc _ fun vx ↦ ?_
    rw [hg]
    exact bindO_enc _ fun vxs ↦ rfl
  | 21 | 24 => rfl
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 11 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 22 | 23 | 25
    | _ + 26 => simp [evStep, none_eq]

/-- The mirror's evaluation step at a node of three children. -/
theorem evStep_three (G : List Tree) (P : (List Tree → Tree → Tree) × (Tree → Tree → Tree))
    (p : Fns) (l : ℕ) (x y z : Tree) (f' g' h' : List Tree → Tree)
    (f g h : List Tree → Option Tree) (hf : ∀ env, f' env = enc (f env))
    (hg : ∀ env, g' env = enc (g env)) (hh : ∀ env, h' env = enc (h env)) (env : List Tree) :
    «Eval.evStep» G P (RoseTree.node l [x, y, z]) [f', g', h'] env =
      enc (evStep G p l [(x, f), (y, g), (z, h)] env) := by
  unfold «Eval.evStep»
  simp only [label_node, arity_node, eq_leaf_ofBool, or_ofBool, and_ofBool, ofBool_label,
    Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.length_cons, List.length_nil,
    Nat.reduceAdd, Const.lcase, child_node, List.getD_cons_zero, List.getD_cons_succ]
  match l with
  | 16 =>
    simp +decide only [evStep, ↓reduceIte]
    rw [hf]
    refine bindO_enc _ fun vc ↦ ?_
    rw [unquote_eq]
    refine bindO_enc _ fun t ↦ ?_
    by_cases ht : t.label = 0
    · simp [const_label, eq_leaf_ofBool, ht, hh]
    · simp [const_label, eq_leaf_ofBool, ht, hg]
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 17 | 18 | 19 | 20 | 21
    | 22 | 23 | 24 | 25 | _ + 26 => simp [evStep, none_eq]

/-- The mirror's evaluation step at a node of more than three children. -/
theorem evStep_more (G : List Tree) (P : (List Tree → Tree → Tree) × (Tree → Tree → Tree))
    (p : Fns) (l : ℕ) (cs : List Tree) (hcs : 3 < cs.length) (F' : Tree → List Tree → Tree)
    (F : Tree → List Tree → Option Tree) (env : List Tree) :
    «Eval.evStep» G P (RoseTree.node l cs) (cs.map F') env =
      enc (evStep G p l (cs.map fun c ↦ (c, F c)) env) := by
  obtain ⟨x, y, z, w, cs, rfl⟩ : ∃ x y z w cs', cs = x :: y :: z :: w :: cs' := by
    rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, cs⟩⟩⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at hcs
    · exact absurd hcs (by omega)
    · exact absurd hcs (by omega)
    · exact absurd hcs (by omega)
    · exact absurd hcs (by omega)
    · exact ⟨x, y, z, w, cs, rfl⟩
  have h₀ : cs.length + 1 + 1 + 1 + 1 ≠ 0 := by omega
  have h₁ : cs.length + 1 + 1 + 1 + 1 ≠ 1 := by omega
  have h₂ : cs.length + 1 + 1 + 1 + 1 ≠ 2 := by omega
  have h₃ : cs.length + 1 + 1 + 1 + 1 ≠ 3 := by omega
  unfold «Eval.evStep»
  simp only [label_node, arity_node, eq_leaf_ofBool, or_ofBool, and_ofBool, ofBool_label,
    Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.length_cons, h₀, h₁, h₂, h₃, and_false,
    or_false, ↓reduceIte]
  match l with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20
    | 21 | 22 | 23 | 24 | 25 | _ + 26 => simp only [evStep, List.map_cons, none_eq]

/-- The mirror's evaluation of a term at a related level. -/
theorem ev_eq (G : List Tree) {P : (List Tree → Tree → Tree) × (Tree → Tree → Tree)} {p : Fns}
    (hP : FnsRel P p) :
    ∀ t env, Const.para («Eval.evStep» G P) t env = enc (RoseTree.para (evStep G p) t env) := by
  refine RoseTree.ind fun l cs ih env ↦ ?_
  rw [Const.para_node, RoseTree.para_node]
  rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, cs⟩⟩⟩⟩
  · exact evStep_nil G P p l env
  · exact evStep_one G hP l x _ _ (ih x (by simp)) env
  · exact evStep_two G hP l x y _ _ _ _ (ih x (by simp)) (ih y (by simp)) env
  · exact evStep_three G P p l x y z _ _ _ _ _ _ (ih x (by simp)) (ih y (by simp))
      (ih z (by simp)) env
  · exact evStep_more G P p l _ (by simp only [List.length_cons]; omega) _ _ env

/-- The mirror's application of a value to a value at a related level. -/
theorem apStep_eq {P : (List Tree → Tree → Tree) × (Tree → Tree → Tree)} {p : Fns}
    (hP : FnsRel P p) (f x : Tree) : «Eval.apStep» P f x = enc (apStep p f x) := by
  rw [← RoseTree.node_label_children f]
  generalize f.label = l
  generalize f.children = cs
  unfold «Eval.apStep»
  simp only [label_node, eq_leaf_ofBool, or_ofBool, ofBool_label, Bool.or_eq_true, beq_iff_eq,
    spine_eq, append_eq, length_eq, constArity_eq, lt_leaf_ofBool, decide_eq_true_eq,
    valApp_eq, sat_eq hP.2, arity_node, and_ofBool, Bool.and_eq_true]
  match l with
  | 10 | 17 | 18 | 21 | 22 | 24 | 25 =>
    simp +decide only [apStep, «Prelude.single», ↓reduceIte, RoseTree.label_node]
    split_ifs with hc <;> simp only [List.length_append, List.length_singleton] at hc ⊢ <;>
      simp [hc, some_eq]
  | 26 =>
    rcases cs with _ | ⟨e, _ | ⟨A, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩⟩
    · simp [apStep, none_eq]
    · simp [apStep, none_eq]
    · simp [apStep, none_eq]
    · simp [apStep, child_node, hP.1]
      rfl
    · simp [apStep, none_eq]
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 11 | 12 | 13 | 14 | 15 | 16 | 19 | 20 | 23
    | _ + 27 => simp [apStep, none_eq]

/-- The mirror's functions at each level are related to the Lean ones. -/
theorem level_rel (G : List Tree) : ∀ n : ℕ, FnsRel («Eval.level» G (leaf n)) (level G n) :=
  Nat.rec ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ fun _ ih ↦
    ⟨fun env t ↦ ev_eq G ih t env, apStep_eq ih⟩

/-- The mirror's evaluation is the Lean one. -/
theorem eval_eq (G : List Tree) (n : ℕ) (env : List Tree) (t : Tree) :
    «Eval.eval» G (leaf n) env t = enc (eval G n env t) := (level_rel G n).1 env t

/-- The mirror's application is the Lean one. -/
theorem apply_eq (G : List Tree) (n : ℕ) (f x : Tree) :
    «Eval.apply» G (leaf n) f x = enc (apply G n f x) := (level_rel G n).2 f x

end GebTests.Prototypes.EvalMirror

end
