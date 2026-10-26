/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ArrayContraction
public import Geb.Prototypes.InteractionNet.GraphConfluence
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# An executable finite graph reducer

The runtime stores a finite indexed cell family and an array of wire partners. It checks
candidate active pairs against the rule table, allocates the selected replacement and
executes array contraction. Searching the finite list of ordered cell pairs gives a
deterministic default schedule. Every successful step represents one graph contraction;
failure to find a redex means the represented graph is normal.

## Main definitions

* {lit}`GraphRuntime.State` — finite cells, their symbols and array-backed wiring.
* {lit}`GraphRuntime.redexAt?` — check one candidate pair against the graph and rule table.
* {lit}`GraphRuntime.step` — execute the first available active pair.

## Main statements

* {lit}`GraphRuntime.step_refines` — a runtime step is a permitted abstract graph step.
* {lit}`GraphRuntime.normal_of_step_none` — an exhausted redex search represents a normal graph.

## Tags

interaction net, runtime, graph reduction, scheduler, refinement, normal form
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.GraphRuntime

open scoped FinEnum

universe u

variable {α : Type u} {arity : α → ℕ} {boundary : ℕ}

/-- Finite indexed cells and their symbols, with array-backed wiring and an ordered boundary. -/
abbrev State (arity : α → ℕ) (boundary : ℕ) :=
  Σ cells : ℕ, Σ label : Fin cells → α, ArrayNet arity label (Fin boundary)

/-- Read a runtime state as a finite graph presentation. -/
def read (n : State arity boundary) : FiniteNet arity boundary := ⟨n.1, n.2.1, n.2.2.read⟩

/-- Store a finite graph presentation in array form. -/
def encode (n : FiniteNet arity boundary) : State arity boundary :=
  ⟨n.1, n.2.1, ArrayNet.encode n.net⟩

/-- Storing and reading a finite graph preserves its complete presentation. -/
@[simp] theorem read_encode (n : FiniteNet arity boundary) : read (encode n) = n := by
  rcases n with ⟨cells, label, n⟩
  simp only [read, encode, ArrayNet.read_encode]

/-- The graph represented by a runtime state, independent of its particular cell allocation. -/
def graph (n : State arity boundary) : Graph arity boundary := Graph.ofNet (read n)

/-- Execute one selected active pair by allocating and rewiring its array representation. -/
def contract {s : PortSystem arity} (n : State arity boundary) (r : s.Redex (read n).net) :
    State arity boundary :=
  ⟨_, _, n.2.2.contract r.active (ArrayNet.encode r.rhs.2.2)⟩

/-- Executing a selected redex refines one abstract graph contraction. -/
theorem contract_step {s : PortSystem arity} (n : State arity boundary)
    (r : s.Redex (read n).net) : FiniteNet.Step s (read n) (read (contract n r)) := by
  refine ⟨r, ⟨?_⟩⟩
  have hi := n.2.2.contractIso r.active (ArrayNet.encode r.rhs.2.2)
  have he := congrArg (fun body ↦ n.2.2.read.contract r.active body)
    (ArrayNet.read_encode r.rhs.2.2)
  exact cast (congrArg (fun body ↦ body.Iso (read (contract n r)).net) he) hi

/-- Check a candidate principal pair and retrieve its finite rule body when one is available. -/
def redexAt? (s : PortSystem arity) (n : State arity boundary) (a b : Fin n.1) :
    Option (s.Redex (read n).net) :=
  if h : n.2.2.read.wiring.partner (PortNet.principal arity n.2.1 a) =
      PortNet.principal arity n.2.1 b then
    match hr : s.rule (n.2.1 a) (n.2.1 b) with
    | none => none
    | some rhs => some ⟨a, b, h, rhs, hr⟩
  else none

/-- Checking the cells of an existing redex finds a rule application. -/
theorem redexAt?_isSome {s : PortSystem arity} {n : State arity boundary}
    (r : s.Redex (read n).net) : (redexAt? s n r.left r.right).isSome := by
  have ha : n.2.2.read.wiring.partner (PortNet.principal arity n.2.1 r.left) =
      PortNet.principal arity n.2.1 r.right := r.active
  have hr : s.rule (n.2.1 r.left) (n.2.1 r.right) = some r.rhs := r.rule_eq
  simp only [redexAt?, dite_eq_left ha]
  split
  · rename_i he
    cases he.symm.trans hr
  · rfl

/-- Enumerate candidate pairs in lexicographic cell-index order. -/
def candidates (cells : ℕ) : List (Fin cells × Fin cells) :=
  (List.finRange cells).flatMap (fun a ↦ (List.finRange cells).map (a, ·))

/-- Every ordered cell pair occurs in the candidate list. -/
theorem mem_candidates {cells : ℕ} (a b : Fin cells) : (a, b) ∈ candidates cells :=
  List.mem_flatMap.mpr ⟨a, List.mem_finRange a,
    List.mem_map.mpr ⟨b, List.mem_finRange b, rfl⟩⟩

/-- Select the first candidate pair that has a principal wire and a permitted rule. -/
def select (s : PortSystem arity) (n : State arity boundary) : Option (s.Redex (read n).net) :=
  (candidates n.1).findSome? (fun p ↦ redexAt? s n p.1 p.2)

/-- An existing redex makes the complete candidate search succeed. -/
theorem select_isSome {s : PortSystem arity} {n : State arity boundary}
    (r : s.Redex (read n).net) : (select s n).isSome :=
  List.findSome?_isSome_iff.mpr ⟨(r.left, r.right), mem_candidates _ _, redexAt?_isSome r⟩

/-- Execute a caller-selected pair when it is an active pair with a permitted rule. -/
def stepAt (s : PortSystem arity) (n : State arity boundary) (a b : Fin n.1) :
    Option (State arity boundary) := (redexAt? s n a b).map (contract n)

/-- A successful caller-selected runtime step is a permitted graph contraction. -/
theorem stepAt_refines {s : PortSystem arity} {n m : State arity boundary} {a b : Fin n.1}
    (h : stepAt s n a b = some m) : Graph.Step s (graph n) (graph m) := by
  obtain ⟨r, _, hm⟩ := Option.map_eq_some_iff.mp h
  subst m
  exact Graph.step_of_net (contract_step n r)

/-- Execute the default schedule's next active pair, if one is available. -/
def step (s : PortSystem arity) (n : State arity boundary) : Option (State arity boundary) :=
  (select s n).map (contract n)

/-- A successful runtime step represents one permitted graph contraction. -/
theorem step_refines {s : PortSystem arity} {n m : State arity boundary}
    (h : step s n = some m) : Graph.Step s (graph n) (graph m) := by
  obtain ⟨r, _, hm⟩ := Option.map_eq_some_iff.mp h
  subst m
  exact Graph.step_of_net (contract_step n r)

/-- If the exhaustive runtime search finds no step, the represented graph is normal. -/
theorem normal_of_step_none {s : PortSystem arity} {n : State arity boundary}
    (h : step s n = none) : Schedule.Normal (Graph.Step s) (graph n) := by
  have hs : select s n = none := Option.map_eq_none_iff.mp h
  intro m hm
  obtain ⟨a, b, ha, _, r, hi⟩ := hm
  obtain ⟨i⟩ := Quotient.exact ha
  have hr := select_isSome (r.map i)
  rw [hs] at hr
  cases hr

/-- A represented normal graph admits no successful runtime step. -/
theorem step_none_of_normal {s : PortSystem arity} {n : State arity boundary}
    (h : Schedule.Normal (Graph.Step s) (graph n)) : step s n = none := by
  cases he : step s n with
  | none => rfl
  | some m => exact (h (graph m) (step_refines he)).elim

end Geb.InteractionNet.GraphRuntime

end
