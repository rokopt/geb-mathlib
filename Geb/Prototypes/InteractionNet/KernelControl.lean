/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelContext
import Geb.Prototypes.InteractionNet.KernelValueShape
import Geb.Prototypes.InteractionNet.Call
import Geb.Prototypes.InteractionNet.Evaluation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# References and lazy conditionals

A reference evaluates its definition in the empty environment. A conditional captures
both branches as thunks and forces only the selected branch. The proofs use compilation
of that selected body in represented environments; they require no evaluation of the
other body.

## Tags

interaction net, kernel, reference, conditional, thunk, laziness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder

/-- A reference dispatches to its definition's represented closed evaluation. -/
theorem callsTo_reference (P : List Tree) (i : ℕ) (t result : Tree) (ht : P[i]? = some t)
    (hb : ∀ {n : ℕ} (ρ : Fin n → Value dataArity),
      ∃ e, compileAt t [i + 1] [] = some e ∧ EvaluatesTo P ρ e result) :
    CallsTo P (.reference i) Eval.Val.unit [] result := by
  intro v hv args hargs
  obtain rfl := rep_unit_value v hv
  obtain rfl := List.forall₂_nil_right_iff.mp hargs
  apply calls_of_body P (.reference i) .unit Fin.elim0 [] [] [] result .nil .nil
  intro n ρ es fs hes hfs
  obtain rfl := List.forall₂_nil_right_iff.mp hes
  obtain rfl := List.forall₂_nil_right_iff.mp hfs
  obtain ⟨e, he, hr⟩ := hb ρ
  exact ⟨e, by simp only [rewrite, ht, Option.bind_some, he], hr⟩

/-- Forcing a thunk evaluates its body in its captured represented environment. -/
theorem forces_thunk (P : List Tree) (site : List ℕ) (b : Tree) {k : ℕ}
    (vs : Fin k → Value dataArity) (env : List Tree) (result : Tree)
    (hen : List.Forall₂ Rep (List.ofFn vs) env)
    (hb : ∀ {n : ℕ} (ρ : Fin n → Value dataArity) (es : List (E n)),
      List.Forall₂ (EvaluatesTo P ρ) es env →
      ∃ e, compileAt b site es = some e ∧ EvaluatesTo P ρ e result) :
    ∃ w, Calls dataArity (program P) .force
      (Term.agent (.inl (.thunk site b k)) vs) [] w ∧ Rep w result := by
  apply calls_of_body P .force (.thunk site b k) vs [] env [] result hen .nil
  intro n ρ es fs hes hfs
  obtain rfl := List.forall₂_nil_right_iff.mp hfs
  exact hb ρ es hes

/-- Selecting a branch reduces to forcing that branch; the unused branch is consumed. -/
theorem calls_choose_of_force (P : List Tree) (l k : ℕ) (vs : Fin k → Value dataArity)
    (a b result : Value dataArity)
    (h : Calls dataArity (program P) .force (if l = 0 then b else a) [] result) :
    Calls dataArity (program P) .choose (Term.agent (.inl (.tree l k)) vs) [a, b] result := by
  let j : Fin (k + 2) := Fin.natAdd k (if l = 0 then 1 else 0)
  let body : E (k + 2) := call .force (Term.var j)
  let ρ : Fin (k + 2) → Value dataArity := Fin.addCases vs [a, b].get
  have hb : (program P).rewrite .choose 2 (.tree l k) = some body := by
    by_cases hl : l = 0 <;>
      simp only [program, List.ofFn_succ, List.ofFn_zero, rewrite, body, j, hl, ↓reduceIte]
    rfl
  apply calls_of_rewrite dataArity (program P) .choose (.tree l k) vs [a, b] body hb result
  have hρ : ρ j = if l = 0 then b else a := by
    by_cases hl : l = 0 <;> simp only [ρ, j, hl, ↓reduceIte, Fin.addCases_right] <;> rfl
  apply evaluates_call dataArity (program P) .force (Term.var j) [] ρ
    (if l = 0 then b else a) result Fin.elim0
  · rw [← hρ]
    exact evaluates_var dataArity (program P) j ρ
  · exact fun i ↦ i.elim0
  · exact h

/-- A conditional evaluates only its selected captured body. Both thunk constructors
capture represented fields, but only the selected body needs a compilation hypothesis. -/
theorem evaluatesTo_choose_thunks (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (c : E n) (t : Tree) (hc : EvaluatesTo P ρ c (Eval.Val.quote t))
    (es : List (E n)) (env : List Tree) (hen : List.Forall₂ (EvaluatesTo P ρ) es env)
    (sa sb : List ℕ) (a b result : Tree)
    (hb : ∀ {m : ℕ} (σ : Fin m → Value dataArity) (fs : List (E m)),
      List.Forall₂ (EvaluatesTo P σ) fs env →
      ∃ e, compileAt (if t.label = 0 then b else a) (if t.label = 0 then sb else sa) fs =
        some e ∧ EvaluatesTo P σ e result) :
    EvaluatesTo P ρ (call .choose c [con (.thunk sa a es.length) es rfl,
      con (.thunk sb b es.length) es rfl]) result := by
  obtain ⟨v, hv, hr⟩ := hc
  obtain rfl := eq_treeValue_of_rep v t hr
  obtain ⟨vs, hvs, henv⟩ := evaluatesTo_environment P ρ es env hen
  let va : Value dataArity := Term.agent (.inl (.thunk sa a es.length)) vs
  let vb : Value dataArity := Term.agent (.inl (.thunk sb b es.length)) vs
  have hf : ∃ w, Calls dataArity (program P) .force (if t.label = 0 then vb else va) [] w ∧
      Rep w result := by
    by_cases ht : t.label = 0
    · rw [ite_eq_left ht]
      apply forces_thunk P sb b vs env result henv
      intro m σ fs hfs
      simpa only [ht, ↓reduceIte] using hb σ fs hfs
    · rw [ite_eq_right ht]
      apply forces_thunk P sa a vs env result henv
      intro m σ fs hfs
      simpa only [ht, ↓reduceIte] using hb σ fs hfs
  obtain ⟨w, hw, hwr⟩ := hf
  have hchoose : Calls dataArity (program P) .choose (treeValue t) [va, vb] w := by
    rw [← RoseTree.node_label_children t, treeValue_node_get]
    exact calls_choose_of_force P t.label t.children.length
      (fun i ↦ treeValue (t.children.get i)) va vb w hw
  have ha := evaluates_con_fields P ρ (.thunk sa a es.length) es rfl vs hvs
  have hb' := evaluates_con_fields P ρ (.thunk sb b es.length) es rfl vs hvs
  let ws : Fin 2 → Value dataArity := Fin.cases va (Fin.cases vb Fin.elim0)
  refine ⟨w, ?_, hwr⟩
  apply evaluates_call dataArity (program P) .choose c
    [con (.thunk sa a es.length) es rfl, con (.thunk sb b es.length) es rfl]
    ρ (treeValue t) w ws hv
  · exact Fin.cases ha (Fin.cases hb' (fun i ↦ i.elim0))
  · simpa only [List.ofFn_succ, List.ofFn_zero, ws, Fin.cases_zero, Fin.cases_succ] using hchoose

end Geb.InteractionNet.Kernel

end
