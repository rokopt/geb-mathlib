/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleGraph
public import Geb.Prototypes.InteractionNet.ConfigGraph
public import Geb.Prototypes.InteractionNet.ProgramCorrect
public import Geb.Prototypes.InteractionNet.GraphRuntimeAdequacy
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# First-order programs in the graph runtime

The first-order compiler registers rules from control agents to data agents, in one
orientation only. Its established rule-linearity theorem therefore permits every rule to
be assembled as a finite graph replacement. A closed expression's initial textual
configuration has one name with two occurrences and compiles directly to a runtime graph.

## Main definitions

* {lit}`FirstOrder.graphSystem` — the first-order program's compiled graph rule table.
* {lit}`FirstOrder.graphInitial` — the finite graph of a closed expression.
* {lit}`FirstOrder.graphRun` — bounded execution by the array runtime.

## Main statements

* {lit}`FirstOrder.system_oriented` — generated rules use only one orientation.
* {lit}`FirstOrder.initial_closed` — the initial wire has both ends present.
* {lit}`FirstOrder.graphRun_refines` — successful executions return reached graph normal forms.

## Tags

interaction net, first-order program, compiler, graph runtime, execution
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.FirstOrder

variable {δ φ : Type} (dataArity : δ → ℕ)

/-- Every registered interaction runs from a control symbol to a data symbol. -/
theorem system_oriented (p : Program (φ := φ) dataArity) :
    (system dataArity p).Oriented := by
  intro a b r h
  cases a with
  | inl a => simp [system] at h
  | inr a =>
    cases b with
    | inl b => rfl
    | inr b =>
      rcases a with k | (e | f) <;> simp [system] at h

/-- The initial configuration of a closed expression has both ends of its sole wire. -/
theorem initial_closed (e : Expr (φ := φ) dataArity 0) :
    (initial dataArity e).Closed := by
  simp only [Config.Closed, Config.names, initial, List.flatMap_cons,
    List.flatMap_nil, Term.names_var, Term.names_agent, List.ofFn_zero, List.ofFn_succ,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
  subst x
  rfl

/-- Compile all generated linear rules to finite graph replacements. -/
def graphSystem (p : Program (φ := φ) dataArity) : PortSystem (netArity (φ := φ) dataArity) :=
  (system dataArity p).toPortSystem (system_rule_linear dataArity p) (system_oriented dataArity p)

/-- Compile the initial evaluator, empty environment and output wire to a finite graph. -/
def graphInitial (e : Expr (φ := φ) dataArity 0) : FiniteNet (netArity (φ := φ) dataArity) 1 :=
  (initial dataArity e).toFiniteNet (initial_closed dataArity e)

/-- Run a closed expression's compiled graph to a normal form within the supplied fuel. -/
def graphRun (p : Program (φ := φ) dataArity) (fuel : ℕ)
    (e : Expr (φ := φ) dataArity 0) :
    Option (GraphRuntime.State (netArity (φ := φ) dataArity) 1) :=
  GraphRuntime.run (graphSystem dataArity p) fuel
    (GraphRuntime.encode (graphInitial dataArity e))

/-- A successful graph execution reaches an abstract normal form under the compiled rules. -/
theorem graphRun_refines (p : Program (φ := φ) dataArity) (fuel : ℕ)
    (e : Expr (φ := φ) dataArity 0) (m : GraphRuntime.State (netArity (φ := φ) dataArity) 1)
    (h : graphRun dataArity p fuel e = some m) :
    Relation.ReflTransGen (Graph.Step (graphSystem dataArity p))
      (Graph.ofNet (graphInitial dataArity e)) (GraphRuntime.graph m) ∧
      Schedule.Normal (Graph.Step (graphSystem dataArity p)) (GraphRuntime.graph m) := by
  simpa only [GraphRuntime.graph, GraphRuntime.read_encode] using GraphRuntime.run_refines h

end Geb.InteractionNet.FirstOrder

end
