/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ExecutionGraphSimulation
public import Geb.Prototypes.InteractionNet.KernelAdequacy
public import Geb.Prototypes.InteractionNet.KernelGraphReadback
import Geb.Prototypes.InteractionNet.Execution
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Typed adequacy of interaction-net graph execution

The textual compiler simulation transfers contextual evaluation to a normalizing graph
schedule. Graph confluence and termination then apply to every schedule of the compiled
program, including the executable partner-array runtime. The whole-net reader returns the
same tree as the checked kernel denotation.

## Main statements

* {lit}`Kernel.graph_normalizes_of_infer` — accepted functions reach their canonical result graph.
* {lit}`Kernel.graph_terminates_of_infer` — every graph schedule from an accepted input terminates.
* {lit}`Kernel.graphRun_of_infer` — the array runtime returns the checked denotation.
* {lit}`Kernel.graphRun_result_eq_of_infer` — every successful bound returns that denotation.
* {lit}`Kernel.graphRun_of_load` — the same result for every loaded global's tree application.

## Tags

bootstrap, kernel, interaction net, graph runtime, adequacy, normalization, denotation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder

/-- Contextual evaluation reaches the corresponding canonical normal tree graph. -/
theorem graph_normalizes_of_evaluates (P : List Tree) (t x y : Tree) (e : E 0)
    (he : compile t [] = some e)
    (hv : Evaluates dataArity (program P) (apply e (literal x)) Fin.elim0 (treeValue y)) :
    ∃ n N, graphInitial t x = some n ∧
      Relation.ReflTransGen (Graph.Step (graphSystem P))
        (Graph.ofNet n) (Graph.ofNet (graphFinal y N)) := by
  obtain ⟨N, hN⟩ := evaluates_initial dataArity (program P) _ _ hv
  let c := FirstOrder.initial dataArity (apply e (literal x))
  let d := Config.singleton (treeTerm y) N
  have hg := (system P).reaches_graph (system_rule_linear dataArity (program P))
    (system_oriented dataArity (program P)) c d
    (FirstOrder.initial_wellFormed dataArity _) (initial_closed dataArity _)
    (Config.singleton_closed _ _ (treeTerm_names y)) hN rfl rfl
  erw [Config.graphAt_refl, Config.graphAt_refl] at hg
  refine ⟨FirstOrder.graphInitial dataArity (apply e (literal x)), N, ?_, hg⟩
  simp only [graphInitial, he, Option.map_some]

/-- A contextual tree result is returned at some finite bound by the partner-array runtime. -/
theorem graphRun_of_evaluates (P : List Tree) (t x y : Tree) (e : E 0)
    (he : compile t [] = some e)
    (hv : Evaluates dataArity (program P) (apply e (literal x)) Fin.elim0 (treeValue y)) :
    ∃ steps, graphRun P steps t x = some y := by
  obtain ⟨n, N, hi, hg⟩ := graph_normalizes_of_evaluates P t x y e he hv
  have hq : Relation.ReflTransGen (Graph.Step (graphSystem P))
      (GraphRuntime.graph (GraphRuntime.encode n)) (Graph.ofNet (graphFinal y N)) := by
    simpa only [GraphRuntime.graph, GraphRuntime.read_encode] using hg
  obtain ⟨steps, m, hm⟩ := GraphRuntime.halts_of_normalizes hq (graphFinal_normal P y N)
  have hr := GraphRuntime.run_readTree_eq_normal graphTreeTag hm hq (graphFinal_normal P y N)
  rw [Graph.readTree_ofNet, graphFinal_readTree] at hr
  exact ⟨steps, by simp only [graphRun, hi, bind, Option.bind_some, hm, hr]⟩

/-- Every accepted closed tree-to-tree term has a graph schedule to its checked denotation. -/
theorem graph_normalizes_of_infer {P : List Tree} {GD : List Glob}
    (hload : Geb.Kernel.load P = some GD) (t : Tree) (f : Tree → Tree)
    (ht : infer GD [] t = some ⟨tArrow tT tT, fun _ ↦ f⟩) (x : Tree) :
    ∃ n N, graphInitial t x = some n ∧
      Relation.ReflTransGen (Graph.Step (graphSystem P))
        (Graph.ofNet n) (Graph.ofNet (graphFinal (f x) N)) := by
  obtain ⟨e, he, hv⟩ := evaluates_of_infer hload t f ht x
  exact graph_normalizes_of_evaluates P t x (f x) e he hv

/-- Every schedule of the compiled graph of an accepted tree-to-tree application terminates. -/
theorem graph_terminates_of_infer {P : List Tree} {GD : List Glob}
    (hload : Geb.Kernel.load P = some GD) (t : Tree) (f : Tree → Tree)
    (ht : infer GD [] t = some ⟨tArrow tT tT, fun _ ↦ f⟩) (x : Tree) :
    ∃ n, graphInitial t x = some n ∧
      Acc (Function.swap (Graph.Step (graphSystem P))) (Graph.ofNet n) := by
  obtain ⟨n, N, hi, hg⟩ := graph_normalizes_of_infer hload t f ht x
  exact ⟨n, hi, Graph.terminates_of_normalizes hg (graphFinal_normal P (f x) N)⟩

/-- Every normal graph schedule of an accepted application reads back its checked denotation. -/
theorem graph_result_eq_of_infer {P : List Tree} {GD : List Glob}
    (hload : Geb.Kernel.load P = some GD) (t : Tree) (f : Tree → Tree)
    (ht : infer GD [] t = some ⟨tArrow tT tT, fun _ ↦ f⟩) (x : Tree)
    (n : FiniteNet (netArity (φ := Op) dataArity) 1) (hi : graphInitial t x = some n)
    (q : Graph (netArity (φ := Op) dataArity) 1)
    (hq : Relation.ReflTransGen (Graph.Step (graphSystem P)) (Graph.ofNet n) q)
    (normal : Schedule.Normal (Graph.Step (graphSystem P)) q) :
    Graph.readTree graphTreeTag q = some (f x) := by
  obtain ⟨n', N, hi', hg⟩ := graph_normalizes_of_infer hload t f ht x
  have he : n' = n := Option.some.inj (hi'.symm.trans hi)
  subst n'
  rw [Graph.normal_unique hq hg normal (graphFinal_normal P (f x) N),
    Graph.readTree_ofNet, graphFinal_readTree]

/-- The executable graph runtime computes every accepted function's checked tree denotation. -/
theorem graphRun_of_infer {P : List Tree} {GD : List Glob}
    (hload : Geb.Kernel.load P = some GD) (t : Tree) (f : Tree → Tree)
    (ht : infer GD [] t = some ⟨tArrow tT tT, fun _ ↦ f⟩) (x : Tree) :
    ∃ steps, graphRun P steps t x = some (f x) := by
  obtain ⟨e, he, hv⟩ := evaluates_of_infer hload t f ht x
  exact graphRun_of_evaluates P t x (f x) e he hv

/-- Every successful execution bound of an accepted function returns its checked denotation. -/
theorem graphRun_result_eq_of_infer {P : List Tree} {GD : List Glob}
    (hload : Geb.Kernel.load P = some GD) (t : Tree) (f : Tree → Tree)
    (ht : infer GD [] t = some ⟨tArrow tT tT, fun _ ↦ f⟩)
    (x y : Tree) (steps : ℕ) (h : graphRun P steps t x = some y) : y = f x := by
  obtain ⟨k, hk⟩ := graphRun_of_infer hload t f ht x
  exact graphRun_result_eq P steps k t x y (f x) h hk

/-- Successful evaluator application is simulated by the executable graph runtime. -/
theorem graphRun_of_eval_apply (P : List Tree) (t x y f : Tree) (n k : ℕ)
    (hev : Eval.eval P n [] t = some f)
    (hap : Eval.apply P k f (Eval.Val.quote x) = some (Eval.Val.quote y)) :
    ∃ steps, graphRun P steps t x = some y := by
  obtain ⟨e, he, hv⟩ := evaluates_of_eval_apply P t x y f n k hev hap
  exact graphRun_of_evaluates P t x y e he hv

/-- Loaded globals compute their assigned tree applications through the graph runtime. -/
theorem graphRun_of_load {P : List Tree} {GD : List Glob}
    (hload : Geb.Kernel.load P = some GD) {i : ℕ} {g : Glob} (hg : GD[i]? = some g) :
    ∃ t, P[i]? = some t ∧ ∀ x y, g.apply x = some y →
      ∃ steps, graphRun P steps t x = some y := by
  obtain ⟨t, n, v, ht, hv, hr⟩ := Eval.eval_apply hload hg
  refine ⟨t, ht, fun x y hy ↦ ?_⟩
  obtain ⟨k, hk⟩ := hr x y hy
  exact graphRun_of_eval_apply P t x y v n k hv hk

end Geb.InteractionNet.Kernel

end
