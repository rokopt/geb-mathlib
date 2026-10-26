/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelSaturation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Simulation of kernel application

Closures evaluate their stored body in an extended captured environment. Partial
applications collect represented arguments until the constant is saturated. Their runtime
constructor stores the same ordered arguments that the evaluator stores in an application
spine, while source paths remain static runtime attributes.

## Main definitions

* {lit}`EvaluationSimulation` — successful source evaluation compiles to represented execution.

## Tags

interaction net, kernel, closure, application, simulation, constant
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder

/-- Every successful source evaluation compiles in every represented expression environment. -/
def EvaluationSimulation (P : List Tree) (ev : List Tree → Tree → Option Tree) : Prop :=
  ∀ env t result, ev env t = some result →
    ∀ {n : ℕ} (ρ : Fin n → Value dataArity) (site : List ℕ) (es : List (E n)),
      List.Forall₂ (EvaluatesTo P ρ) es env →
      ∃ e, compileAt t site es = some e ∧ EvaluatesTo P ρ e result

private theorem spine_foldl (h : Tree) (args : List Tree) :
    Eval.spine (args.foldl Eval.Val.app h) = ((Eval.spine h).1, (Eval.spine h).2 ++ args) := by
  apply List.rec (motive := fun args ↦ ∀ h, Eval.spine (args.foldl Eval.Val.app h) =
    ((Eval.spine h).1, (Eval.spine h).2 ++ args))
    (fun _ ↦ by simp only [List.foldl_nil, List.append_nil]) (fun a as ih h ↦ ?_) args h
  rw [List.foldl_cons, ih, Eval.spine_app]
  simp only [List.append_assoc, List.singleton_append]

/-- Expanding a runtime constant's supplied arguments gives exactly its evaluator spine. -/
theorem spine_partial {h : Tree} (hh : ConstantHead h) (args : List Tree) :
    Eval.spine (args.foldl Eval.Val.app h) = (h, args) := by
  have hn : h.label ≠ Label.app := by
    rcases hh with hh | hh | hh | hh | hh | hh <;> rw [hh] <;> decide
  have hs : Eval.spine h = (h, []) := by
    simpa only [RoseTree.node_label_children] using Eval.spine_node hn h.children
  rw [spine_foldl, hs]
  rfl

/-- Application to a represented constant spine checks the same accumulated argument count. -/
theorem apStep_partial (p : Eval.Fns) {h : Tree} (hh : ConstantHead h)
    (args : List Tree) (x : Tree) :
    Eval.apStep p (args.foldl Eval.Val.app h) x =
      if (args ++ [x]).length < Eval.arity h then some (Eval.Val.app (args.foldl Eval.Val.app h) x)
      else Eval.sat p.2 h (args ++ [x]) := by
  have hs := spine_partial hh args
  cases args with
  | nil =>
    change Eval.spine h = (h, []) at hs
    rcases hh with hh | hh | hh | hh | hh | hh <;>
      simp only [List.foldl_nil, List.nil_append, Eval.apStep, hh, hs]
  | cons a as =>
    have hl : ((a :: as).foldl Eval.Val.app h).label = Label.app := by
      rw [spineValue_label]
      rfl
    simp only [Eval.apStep, hl, hs]

/-- One evaluator application layer is simulated when source evaluation and applications
in the preceding layer are simulated. -/
theorem application_step_simulation (P : List Tree) (p : Eval.Fns)
    (hev : EvaluationSimulation P p.1) (hap : ApplicationSimulation P p.2) :
    ApplicationSimulation P (Eval.apStep p) := by
  intro f x result h v hv args hargs
  obtain ⟨vx, tail, hx, ht, rfl⟩ := List.forall₂_cons_right_iff.mp hargs
  obtain rfl := List.forall₂_nil_right_iff.mp ht
  cases v with
  | pure x => exact x.elim
  | liftBind a vs =>
    cases a with
    | inr n => exact False.elim hv
    | inl a =>
      cases a with
      | tree => obtain ⟨ts, _, rfl⟩ := hv; cases h
      | unit => obtain rfl := hv; cases h
      | pair => obtain ⟨a, b, _, _, rfl⟩ := hv; cases h
      | nil => obtain rfl := hv; cases h
      | cons => obtain ⟨a, b, _, _, rfl⟩ := hv; cases h
      | thunk => exact False.elim hv
      | closure site A b k =>
        obtain ⟨en, hen, rfl⟩ := hv
        change p.1 (x :: (RoseTree.node 0 (List.ofFn en)).children) b = some result at h
        rw [RoseTree.children_node] at h
        apply calls_of_body P .apply (.closure site A b k) vs [vx] (List.ofFn en) [x]
          result (fields_related Rep vs en hen) (.cons hx .nil)
        intro m ρ cs rs hcs hrs
        obtain ⟨e, rest, he, hr, rfl⟩ := List.forall₂_cons_right_iff.mp hrs
        obtain rfl := List.forall₂_nil_right_iff.mp hr
        exact hev (x :: List.ofFn en) b result h ρ site (e :: cs) (.cons he hcs)
      | partialApp site hd k =>
        obtain ⟨hh, en, hen, rfl⟩ := hv
        rw [apStep_partial p hh] at h
        apply calls_of_body P .apply (.partialApp site hd k) vs [vx] (List.ofFn en) [x]
          result (fields_related Rep vs en hen) (.cons hx .nil)
        intro m ρ cs rs hcs hrs
        obtain ⟨e, rest, he, hr, rfl⟩ := List.forall₂_cons_right_iff.mp hrs
        obtain rfl := List.forall₂_nil_right_iff.mp hr
        have hrel := List.rel_append hcs (.cons he .nil)
        have hlen : (cs ++ [e]).length = (List.ofFn en ++ [x]).length := hrel.length_eq
        by_cases hlt : (List.ofFn en ++ [x]).length < Eval.arity hd
        · rw [ite_eq_left hlt] at h
          obtain rfl := Option.some.inj h
          refine ⟨con (.partialApp site hd (cs ++ [e]).length) (cs ++ [e]) rfl, ?_, ?_⟩
          · exact ite_eq_left (by simpa only [hlen] using hlt)
          · simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
              evaluatesTo_partial P ρ site hd hh (cs ++ [e]) (List.ofFn en ++ [x]) hrel
        · rw [ite_eq_right hlt] at h
          obtain ⟨body, hbody, hb⟩ :=
            saturated_evaluatesTo P p.2 hap ρ site hd (cs ++ [e]) (List.ofFn en ++ [x])
              result hrel h
          refine ⟨body, ?_, hb⟩
          have hn : ¬(cs ++ [e]).length < Eval.arity hd := by simpa only [hlen] using hlt
          exact (ite_eq_right hn).trans hbody

end Geb.InteractionNet.Kernel

end
