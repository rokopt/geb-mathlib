/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.CalculusGraphSimulation
public import Geb.Prototypes.InteractionNet.CalculusInterface
public import Geb.Prototypes.InteractionNet.ConfigGraphNormal
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Complete textual executions refine graph execution

Closure, well-formedness and interface size are invariant along textual execution. Each
textual step can therefore use the graph simulation theorem, yielding a graph schedule
from the input to the compiled result. If that result has no equations, it is graph-normal;
the graph diamond theorem then ensures termination of every graph schedule from the input.

## Main statements

* {lit}`System.run_graph_reaches` — every bounded textual execution has a graph execution.
* {lit}`System.reaches_graph` — finite textual reachability transfers to compiled graphs.
* {lit}`System.graph_terminates_of_reaches` — a textual tree result makes graph reduction terminate.

## Tags

interaction net, compiler, execution, normalization, graph, schedule, refinement
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α : Type} {arity : α → ℕ} {boundary : ℕ}

/-- Every finite textual run is simulated at the input's fixed ordered graph boundary. -/
theorem System.run_graph_reaches (s : System arity) (linear : s.Linear) (oriented : s.Oriented)
    (c : Config arity) (hw : c.WellFormed) (hc : c.Closed)
    (bc : c.interface.length = boundary) (n : ℕ) :
    Relation.ReflTransGen (Graph.Step (s.toPortSystem linear oriented))
      (c.graphAt hc bc) ((s.run n c).graphAt (s.run_closed linear c hw hc n)
        ((s.run_interface_length c n).trans bc)) := by
  suffices h : ∀ n (hd : (s.run n c).Closed) (bd : (s.run n c).interface.length = boundary),
      Relation.ReflTransGen (Graph.Step (s.toPortSystem linear oriented))
        (c.graphAt hc bc) ((s.run n c).graphAt hd bd) from h n _ _
  refine Nat.rec (fun _ _ ↦ .refl) (fun n ih hd bd ↦ ?_)
  change ((s.step (s.run n c)).getD (s.run n c)).Closed at hd
  change ((s.step (s.run n c)).getD (s.run n c)).interface.length = boundary at bd
  change Relation.ReflTransGen _ _
    (((s.step (s.run n c)).getD (s.run n c)).graphAt hd bd)
  revert hd bd
  cases h : s.step (s.run n c) with
  | none => exact ih
  | some d =>
    intro hd bd
    let hn := s.run_closed linear c hw hc n
    let bn := (s.run_interface_length c n).trans bc
    exact (ih hn bn).trans
      (s.step_graph_reaches linear oriented (s.run n c) d hn hd h bn bd)

/-- Every reached textual configuration has a corresponding finite execution of compiled graphs. -/
theorem System.reaches_graph (s : System arity) (linear : s.Linear) (oriented : s.Oriented)
    (c d : Config arity) (hw : c.WellFormed) (hc : c.Closed) (hd : d.Closed)
    (h : s.Reaches c d) (bc : c.interface.length = boundary)
    (bd : d.interface.length = boundary) :
    Relation.ReflTransGen (Graph.Step (s.toPortSystem linear oriented))
      (c.graphAt hc bc) (d.graphAt hd bd) := by
  obtain ⟨n, rfl⟩ := h
  exact s.run_graph_reaches linear oriented c hw hc bc n

/-- An equation-free configuration is graph-normal at any proof of its external boundary size. -/
theorem Config.graphAt_normal (c : Config arity) (closed : c.Closed)
    (empty : c.equations = []) (s : PortSystem arity) (bc : c.interface.length = boundary) :
    Schedule.Normal (Graph.Step s) (c.graphAt closed bc) := by
  cases bc
  rw [Config.graphAt_refl]
  exact c.graph_normal_of_equations_eq_nil closed empty s

/-- Reaching an equation-free textual result makes every compiled graph schedule terminate. -/
theorem System.graph_terminates_of_reaches (s : System arity) (linear : s.Linear)
    (oriented : s.Oriented) (c d : Config arity) (hw : c.WellFormed)
    (hc : c.Closed) (hd : d.Closed) (h : s.Reaches c d) (empty : d.equations = [])
    (bc : c.interface.length = boundary) (bd : d.interface.length = boundary) :
    Acc (Function.swap (Graph.Step (s.toPortSystem linear oriented))) (c.graphAt hc bc) :=
  Graph.terminates_of_normalizes (s.reaches_graph linear oriented c d hw hc hd h bc bd)
    (d.graphAt_normal hd empty _ bd)

end Geb.InteractionNet

end
