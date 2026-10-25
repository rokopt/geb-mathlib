/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelEvaluation
public import Geb.Prototypes.InteractionNet.Normalization
import Geb.Prototypes.InteractionNet.Execution
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Adequacy of the kernel interaction system

Every successful computation of the kernel evaluator is simulated by the compiled
interaction system. The evaluator's logical relation then supplies termination and the
result for every accepted closed program from trees to trees. Consequently the executable
sequential reducer reaches a normal configuration whose read-back is that denotation.

## Main statements

* {lit}`level_simulation` — evaluation and application are simulated at every fuel level.
* {lit}`normalizes_of_infer` — the compiled term reaches the canonical normal tree configuration.
* {lit}`run_of_infer` — every accepted closed tree-to-tree term computes its denotation.
* {lit}`result_eq_of_infer` — every successful bounded run has that same result.
* {lit}`run_of_load` — the same conclusion for every global of a loaded program.

## Tags

interaction net, kernel, compiler, adequacy, normalization, denotation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder

/-- Both components of every evaluator level are simulated by the interaction system. -/
theorem level_simulation (P : List Tree) : ∀ n,
    EvaluationSimulation P (Eval.level P n).1 ∧
      ApplicationSimulation P (Eval.level P n).2 := by
  refine Nat.rec ?_ (fun n ih ↦ ?_)
  · exact ⟨(fun _ _ _ h ↦ by cases h), (fun _ _ _ h ↦ by cases h)⟩
  · exact ⟨evaluation_step_simulation P (Eval.level P n) ih.1 ih.2,
      application_step_simulation P (Eval.level P n) ih.1 ih.2⟩

/-- A successful evaluator application gives contextual evaluation to the canonical tree value. -/
theorem evaluates_of_eval_apply (P : List Tree) (t x y f : Tree) (n k : ℕ)
    (hev : Eval.eval P n [] t = some f)
    (hap : Eval.apply P k f (Eval.Val.quote x) = some (Eval.Val.quote y)) :
    ∃ e : E 0, compile t [] = some e ∧
      Evaluates dataArity (program P) (apply e (literal x)) Fin.elim0 (treeValue y) := by
  obtain ⟨e, he, hr⟩ := (level_simulation P n).1 [] t f hev Fin.elim0 [0] [] .nil
  have hc := (level_simulation P k).2 f (Eval.Val.quote x) (Eval.Val.quote y) hap
  obtain ⟨v, hv, hrep⟩ := evaluatesTo_apply P Fin.elim0 e (literal x) f
    (Eval.Val.quote x) (Eval.Val.quote y) hr (evaluatesTo_literal P Fin.elim0 x) hc
  exact ⟨e, he, (eq_treeValue_of_rep v y hrep) ▸ hv⟩

/-- Every tree result computed by the evaluator is obtained by the executable net reducer. -/
theorem run_of_eval_apply (P : List Tree) (t x y f : Tree) (n k : ℕ)
    (hev : Eval.eval P n [] t = some f)
    (hap : Eval.apply P k f (Eval.Val.quote x) = some (Eval.Val.quote y)) :
    ∃ steps, run P steps t x = some y := by
  obtain ⟨e, he, hr⟩ := evaluates_of_eval_apply P t x y f n k hev hap
  exact run_of_evaluates P t x y e he hr

/-- The checker denotation of a closed tree-to-tree term is its contextual net result. -/
theorem evaluates_of_infer {P : List Tree} {GD : List Glob} (hload : Geb.Kernel.load P = some GD)
    (t : Tree) (f : Tree → Tree)
    (ht : infer GD [] t = some ⟨tArrow tT tT, fun _ ↦ f⟩) (x : Tree) :
    ∃ e : E 0, compile t [] = some e ∧
      Evaluates dataArity (program P) (apply e (literal x)) Fin.elim0 (treeValue (f x)) := by
  obtain ⟨n, v, hv, hr⟩ := Eval.fundamental P GD (Eval.load_rel hload)
    t [] ⟨tArrow tT tT, fun _ ↦ f⟩ ht [] () rfl
  obtain ⟨k, w, hw, hrw⟩ := (Eval.rel_arrow P tT tT v f).mp hr (Eval.Val.quote x) x rfl
  have he : w = Eval.Val.quote (f x) := (Eval.rel_tree P w (f x)).mp hrw
  exact evaluates_of_eval_apply P t x (f x) v n k hv (hw.trans (congrArg some he))

/-- Every accepted closed tree-to-tree term reaches its canonical normal tree configuration. -/
theorem normalizes_of_infer {P : List Tree} {GD : List Glob}
    (hload : Geb.Kernel.load P = some GD) (t : Tree) (f : Tree → Tree)
    (ht : infer GD [] t = some ⟨tArrow tT tT, fun _ ↦ f⟩) (x : Tree) :
    ∃ c N, initial t x = some c ∧
      (system P).Reaches c ⟨[treeTerm (f x)], [], N⟩ ∧
      (system P).Normal ⟨[treeTerm (f x)], [], N⟩ := by
  obtain ⟨e, he, hr⟩ := evaluates_of_infer hload t f ht x
  obtain ⟨N, hN⟩ := evaluates_initial dataArity (program P) _ _ hr
  exact ⟨FirstOrder.initial dataArity (apply e (literal x)), N,
    by simp only [initial, he, Option.map_some], hN,
    (system P).normal_of_equations_eq_nil _ rfl⟩

/-- Every accepted closed tree-to-tree term finishes at its denotation on every input. -/
theorem run_of_infer {P : List Tree} {GD : List Glob} (hload : Geb.Kernel.load P = some GD)
    (t : Tree) (f : Tree → Tree)
    (ht : infer GD [] t = some ⟨tArrow tT tT, fun _ ↦ f⟩) (x : Tree) :
    ∃ steps, run P steps t x = some (f x) := by
  obtain ⟨e, he, hr⟩ := evaluates_of_infer hload t f ht x
  exact run_of_evaluates P t x (f x) e he hr

/-- A successful bounded run of an accepted closed term returns exactly its denotation. -/
theorem result_eq_of_infer {P : List Tree} {GD : List Glob}
    (hload : Geb.Kernel.load P = some GD) (t : Tree) (f : Tree → Tree)
    (ht : infer GD [] t = some ⟨tArrow tT tT, fun _ ↦ f⟩)
    (x y : Tree) (steps : ℕ) (h : run P steps t x = some y) : y = f x := by
  obtain ⟨k, hk⟩ := run_of_infer hload t f ht x
  have h₁ := run_add_of_eq_some P steps k t x y h
  have h₂ := run_add_of_eq_some P k steps t x (f x) hk
  rw [Nat.add_comm k steps] at h₂
  exact Option.some.inj (h₁.symm.trans h₂)

/-- Each loaded global computes every tree result assigned by its checked denotation. -/
theorem run_of_load {P : List Tree} {GD : List Glob} (hload : Geb.Kernel.load P = some GD)
    {i : ℕ} {g : Glob} (hg : GD[i]? = some g) :
    ∃ t, P[i]? = some t ∧ ∀ x y, g.apply x = some y →
      ∃ steps, run P steps t x = some y := by
  obtain ⟨t, n, v, ht, hv, hr⟩ := Eval.eval_apply hload hg
  refine ⟨t, ht, fun x y hy ↦ ?_⟩
  obtain ⟨k, hk⟩ := hr x y hy
  exact run_of_eval_apply P t x y v n k hv hk

end Geb.InteractionNet.Kernel

end
