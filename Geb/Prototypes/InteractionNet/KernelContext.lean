/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelValue
import Geb.Prototypes.InteractionNet.Call
import Geb.Prototypes.InteractionNet.Evaluation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Composing represented kernel evaluations

The contextual normalization theorems apply to kernel expressions through their finite
lists of fields and arguments. These lemmas assemble represented data values, capture an
evaluated environment, and apply a represented call to evaluated expressions.

## Tags

interaction net, kernel, evaluation, environment, composition
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder
open scoped FinEnum

private theorem ofFn_get_cast {α : Type} {n : ℕ} (xs : List α) (h : n = xs.length) :
    (List.ofFn fun i : Fin n ↦ xs.get (Fin.cast h i)) = xs := by
  subst n
  exact List.ofFn_get xs

/-- Pointwise related finite fields give related lists in port order. -/
theorem fields_related {α β : Type} (R : α → β → Prop) {n : ℕ}
    (xs : Fin n → α) (ys : Fin n → β) (h : ∀ i, R (xs i) (ys i)) :
    List.Forall₂ R (List.ofFn xs) (List.ofFn ys) := by
  apply List.forall₂_of_length_eq_of_get (by simp only [List.length_ofFn])
  intro i hi hj
  simpa only [List.get_eq_getElem, List.getElem_ofFn] using
    h ⟨i, by simpa only [List.length_ofFn] using hi⟩

/-- Successful sequencing identifies the result of every optional computation in order. -/
theorem sequence_related {α : Type} (xs : List (Option α)) (ys : List α)
    (h : xs.mapM id = some ys) : List.Forall₂ (fun x y ↦ x = some y) xs ys := by
  apply List.rec (motive := fun xs ↦ ∀ ys, xs.mapM id = some ys →
    List.Forall₂ (fun x y ↦ x = some y) xs ys)
    (fun ys h ↦ by obtain rfl := Option.some.inj h; exact .nil)
    (fun x xs ih ys h ↦ ?_) xs ys h
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨y, hy, ys', hys, rfl⟩ := h
  exact .cons hy (ih ys' hys)

/-- Assemble a constructor after evaluating the expressions at its ports. -/
theorem evaluates_con_fields (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (a : Constructor) (es : List (E n)) (h : es.length = dataArity a)
    (vs : Fin (dataArity a) → Value dataArity)
    (hv : ∀ i, Evaluates dataArity (program P) (es.get (Fin.cast h.symm i)) ρ (vs i)) :
    Evaluates dataArity (program P) (con a es h) ρ (Term.agent (.inl a) vs) :=
  evaluates_con dataArity (program P) a _ ρ vs hv

/-- The unit expression represents the evaluator's unit value. -/
theorem evaluatesTo_unit (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity) :
    EvaluatesTo P ρ unit Eval.Val.unit :=
  ⟨Term.agent (.inl .unit) Fin.elim0,
    evaluates_con_fields P ρ .unit [] rfl Fin.elim0 (fun i ↦ i.elim0), rfl⟩

/-- Pair construction composes the represented evaluations of its two fields. -/
theorem evaluatesTo_pair (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (a b : E n) (x y : Tree) (ha : EvaluatesTo P ρ a x) (hb : EvaluatesTo P ρ b y) :
    EvaluatesTo P ρ (pair a b) (Eval.Val.pair x y) := by
  obtain ⟨v, hv, hr⟩ := ha
  obtain ⟨w, hw, hs⟩ := hb
  let vs : Fin 2 → Value dataArity := Fin.cases v (Fin.cases w Fin.elim0)
  refine ⟨Term.agent (.inl .pair) vs, ?_, x, y, hr, hs, rfl⟩
  exact evaluates_con_fields P ρ .pair [a, b] rfl vs
    (Fin.cases hv (Fin.cases hw (fun i ↦ i.elim0)))

/-- An empty list represents the evaluator's empty list at the same element type. -/
theorem evaluatesTo_nil (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity) (A : Tree) :
    EvaluatesTo P ρ (nil A) (RoseTree.node Label.nil [A]) :=
  ⟨Term.agent (.inl (.nil A)) Fin.elim0,
    evaluates_con_fields P ρ (.nil A) [] rfl Fin.elim0 (fun i ↦ i.elim0), rfl⟩

/-- List construction composes the represented evaluations of its head and tail. -/
theorem evaluatesTo_cons (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (a b : E n) (x xs : Tree) (ha : EvaluatesTo P ρ a x) (hb : EvaluatesTo P ρ b xs) :
    EvaluatesTo P ρ (cons a b) (RoseTree.node Label.cons [x, xs]) := by
  obtain ⟨v, hv, hr⟩ := ha
  obtain ⟨w, hw, hs⟩ := hb
  let vs : Fin 2 → Value dataArity := Fin.cases v (Fin.cases w Fin.elim0)
  refine ⟨Term.agent (.inl .cons) vs, ?_, x, xs, hr, hs, rfl⟩
  exact evaluates_con_fields P ρ .cons [a, b] rfl vs
    (Fin.cases hv (Fin.cases hw (fun i ↦ i.elim0)))

/-- A list of represented evaluations yields a represented kernel list value. -/
theorem evaluatesTo_list (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (A : Tree) (es : List (E n)) (vs : List Tree)
    (h : List.Forall₂ (EvaluatesTo P ρ) es vs) :
    EvaluatesTo P ρ (list A es) (Eval.Val.ofList A vs) := by
  apply List.Forall₂.rec (motive := fun es vs _ ↦
    EvaluatesTo P ρ (list A es) (Eval.Val.ofList A vs))
    (evaluatesTo_nil P ρ A) (fun he _ ih ↦ ?_) h
  exact evaluatesTo_cons P ρ _ _ _ _ he ih

/-- Capturing an evaluated environment represents the evaluator's closure. -/
theorem evaluatesTo_closure (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (site : List ℕ) (A b : Tree) (es : List (E n)) (en : List Tree)
    (h : List.Forall₂ (EvaluatesTo P ρ) es en) :
    EvaluatesTo P ρ (con (.closure site A b es.length) es rfl) (Eval.Val.clo en A b) := by
  let rs : Fin es.length → Tree := fun i ↦ en.get (Fin.cast h.length_eq i)
  obtain ⟨vs, hv, hr⟩ := evaluatesTo_fields P ρ es.get rs
    (fun i ↦ h.get i.isLt (by simpa only [← h.length_eq] using i.isLt))
  refine ⟨Term.agent (.inl (.closure site A b es.length)) vs,
    evaluates_con_fields P ρ (.closure site A b es.length) es rfl vs hv, rs, hr, ?_⟩
  rw [ofFn_get_cast en h.length_eq]

/-- Capturing supplied arguments represents the same evaluator application spine. -/
theorem evaluatesTo_partial (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (site : List ℕ) (hd : Tree) (hh : ConstantHead hd) (es : List (E n)) (args : List Tree)
    (h : List.Forall₂ (EvaluatesTo P ρ) es args) :
    EvaluatesTo P ρ (con (.partialApp site hd es.length) es rfl)
      (args.foldl Eval.Val.app hd) := by
  let rs : Fin es.length → Tree := fun i ↦ args.get (Fin.cast h.length_eq i)
  obtain ⟨vs, hv, hr⟩ := evaluatesTo_fields P ρ es.get rs
    (fun i ↦ h.get i.isLt (by simpa only [← h.length_eq] using i.isLt))
  refine ⟨Term.agent (.inl (.partialApp site hd es.length)) vs,
    evaluates_con_fields P ρ (.partialApp site hd es.length) es rfl vs hv, hh, rs, hr, ?_⟩
  rw [ofFn_get_cast args h.length_eq]

/-- A tree constructor composes represented child-tree evaluations. -/
theorem evaluatesTo_tree (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (l : ℕ) (es : List (E n)) (ts : List Tree)
    (h : List.Forall₂ (fun e t ↦ EvaluatesTo P ρ e (Eval.Val.quote t)) es ts) :
    EvaluatesTo P ρ (tree l es) (Eval.Val.quote (RoseTree.node l ts)) := by
  let rs : Fin es.length → Tree := fun i ↦ ts.get (Fin.cast h.length_eq i)
  obtain ⟨vs, hv, hr⟩ := evaluatesTo_fields P ρ es.get (fun i ↦ Eval.Val.quote (rs i))
    (fun i ↦ h.get i.isLt (by simpa only [← h.length_eq] using i.isLt))
  refine ⟨Term.agent (.inl (.tree l es.length)) vs,
    evaluates_con_fields P ρ (.tree l es.length) es rfl vs hv, rs, hr, ?_⟩
  rw [ofFn_get_cast ts h.length_eq]

/-- A call represents an evaluator result for every representation of its arguments. -/
def CallsTo (P : List Tree) (f : Op) (x : Tree) (xs : List Tree) (y : Tree) : Prop :=
  ∀ v, Rep v x → ∀ vs, List.Forall₂ Rep vs xs →
    ∃ w, Calls dataArity (program P) f v vs w ∧ Rep w y

/-- A represented expression environment has closed field values representing its raw entries. -/
theorem evaluatesTo_environment (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (es : List (E n)) (env : List Tree) (h : List.Forall₂ (EvaluatesTo P ρ) es env) :
    ∃ vs : Fin es.length → Value dataArity,
      (∀ i, Evaluates dataArity (program P) (es.get i) ρ (vs i)) ∧
      List.Forall₂ Rep (List.ofFn vs) env := by
  let rs : Fin es.length → Tree := fun i ↦ env.get (Fin.cast h.length_eq i)
  obtain ⟨vs, hv, hr⟩ := evaluatesTo_fields P ρ es.get rs
    (fun i ↦ h.get i.isLt (by simpa only [← h.length_eq] using i.isLt))
  refine ⟨vs, hv, ?_⟩
  apply List.forall₂_of_length_eq_of_get
  · simpa only [List.length_ofFn] using h.length_eq
  · intro i hi hj
    simpa only [List.get_eq_getElem, List.getElem_ofFn, rs, Fin.val_cast] using
      hr ⟨i, by simpa only [List.length_ofFn] using hi⟩

/-- Represented arguments and a represented call compose to evaluate a call expression. -/
theorem evaluatesTo_call (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (f : Op) (e : E n) (es : List (E n)) (x y : Tree) (xs : List Tree)
    (he : EvaluatesTo P ρ e x) (hes : List.Forall₂ (EvaluatesTo P ρ) es xs)
    (hc : CallsTo P f x xs y) : EvaluatesTo P ρ (call f e es) y := by
  obtain ⟨v, hv, hr⟩ := he
  obtain ⟨vs, hvs, hs⟩ := evaluatesTo_environment P ρ es xs hes
  obtain ⟨w, hw, hwr⟩ := hc v hr (List.ofFn vs) hs
  exact ⟨w, evaluates_call dataArity (program P) f e es ρ v w vs hv hvs hw, hwr⟩

/-- Represented function and argument evaluations compose with a represented application. -/
theorem evaluatesTo_apply (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (f e : E n) (x y z : Tree) (hf : EvaluatesTo P ρ f x) (he : EvaluatesTo P ρ e y)
    (hc : CallsTo P .apply x [y] z) : EvaluatesTo P ρ (apply f e) z :=
  evaluatesTo_call P ρ .apply f [e] x z [y] hf (.cons he .nil) hc

/-- A list of variables represents the corresponding entries of its closed environment. -/
theorem evaluatesTo_variables (P : List Tree) {n k : ℕ} (ρ : Fin n → Value dataArity)
    (is : Fin k → Fin n) (xs : List Tree)
    (h : List.Forall₂ Rep (List.ofFn fun i ↦ ρ (is i)) xs) :
    List.Forall₂ (EvaluatesTo P ρ) (List.ofFn fun i ↦ Term.var (is i)) xs := by
  apply List.forall₂_of_length_eq_of_get
  · simpa only [List.length_ofFn] using h.length_eq
  · intro i hi hj
    have hi' : i < k := by simpa only [List.length_ofFn] using hi
    refine ⟨ρ (is ⟨i, hi'⟩), ?_, ?_⟩
    · simpa only [List.get_eq_getElem, List.getElem_ofFn] using
        evaluates_var dataArity (program P) (is ⟨i, hi'⟩) ρ
    · simpa only [List.get_eq_getElem, List.getElem_ofFn] using
        h.get (by simpa only [List.length_ofFn] using hi') hj

/-- Constructor dispatch preserves representation whenever its body does so for arbitrary
expressions representing the constructor fields and further arguments. -/
theorem calls_of_body (P : List Tree) (f : Op) (a : Constructor)
    (vs : Fin (dataArity a) → Value dataArity) (args : List (Value dataArity))
    (cs rs : List Tree) (result : Tree)
    (hcs : List.Forall₂ Rep (List.ofFn vs) cs) (hrs : List.Forall₂ Rep args rs)
    (hb : ∀ {n : ℕ} (ρ : Fin n → Value dataArity) (es fs : List (E n)),
      List.Forall₂ (EvaluatesTo P ρ) es cs → List.Forall₂ (EvaluatesTo P ρ) fs rs →
      ∃ body, rewrite P f a es fs = some body ∧ EvaluatesTo P ρ body result) :
    ∃ w, Calls dataArity (program P) f (Term.agent (.inl a) vs) args w ∧ Rep w result := by
  let ρ : Fin (dataArity a + args.length) → Value dataArity := Fin.addCases vs args.get
  let es : List (E (dataArity a + args.length)) :=
    List.ofFn fun i ↦ Term.var (Fin.castAdd args.length i)
  let fs : List (E (dataArity a + args.length)) :=
    List.ofFn fun i ↦ Term.var (Fin.natAdd (dataArity a) i)
  have hes : List.Forall₂ (EvaluatesTo P ρ) es cs :=
    evaluatesTo_variables P ρ (Fin.castAdd args.length) cs
      (by simpa only [ρ, Fin.addCases_left] using hcs)
  have hfs : List.Forall₂ (EvaluatesTo P ρ) fs rs :=
    evaluatesTo_variables P ρ (Fin.natAdd (dataArity a)) rs
      (by simpa only [ρ, Fin.addCases_right, List.ofFn_get] using hrs)
  obtain ⟨body, hbody, w, hw, hr⟩ := hb ρ es fs hes hfs
  exact ⟨w, calls_of_rewrite dataArity (program P) f a vs args body hbody w hw, hr⟩

end Geb.InteractionNet.Kernel

end
