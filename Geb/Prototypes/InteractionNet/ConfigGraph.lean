/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Calculus
public import Geb.Prototypes.InteractionNet.ContractionIso
public import Geb.Prototypes.InteractionNet.EquationGraph
public import Geb.Prototypes.InteractionNet.FiniteCells
public import Geb.Prototypes.InteractionNet.NamedWiring
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Closed textual configurations as finite graphs

A closed configuration has exactly two occurrences of every name that it uses. Its
interface terms become the ordered external boundary; equation roots are joined in pairs;
and equally named leaf occurrences are joined into wires. The resulting finite graph has
the same ordered interface, includes every syntax cell and retains closed wire components.

The allocation supply is irrelevant to graph identity. It remains part of the textual
configuration because later textual interactions allocate fresh names.

## Main definitions

* {lit}`Config.Closed` — every used wire name has exactly two ends.
* {lit}`Config.toFiniteNet` — assemble a closed configuration as a finite port graph.

## Main statements

* {lit}`Config.graphLeaf_count` — the graph forest preserves textual wire multiplicities.

## Tags

interaction net, configuration, compiler, graph, interface, wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- Every name occurring in the configuration has exactly two ends. -/
def Closed (c : Config arity) : Prop := ∀ x ∈ c.names, c.names.count x = 2

/-- A closed configuration has zero or two occurrences of each possible wire name. -/
theorem Closed.count {c : Config arity} (h : c.Closed) (x : ℕ) :
    c.names.count x = 0 ∨ c.names.count x = 2 := by
  by_cases hx : x ∈ c.names
  · exact Or.inr (h x hx)
  · exact Or.inl (List.count_eq_zero_of_not_mem hx)

/-- The interface roots followed by both sides of every equation. -/
abbrev GraphRoot (c : Config arity) := Fin c.interface.length ⊕ EquationGraph.Root c.equations

/-- Translate every interface term and equation side into its term fragment. -/
def graphFragments (c : Config arity) : c.GraphRoot → TermFragment arity ℕ :=
  Sum.elim (fun i ↦ (c.interface.get i).fragment) (EquationGraph.fragments c.equations)

/-- The syntax order used to enumerate the configuration's roots. -/
def graphRootOrder (c : Config arity) : List c.GraphRoot :=
  (List.finRange c.interface.length).map Sum.inl ++
    (EquationGraph.order c.equations).map Sum.inr

/-- The root enumeration contains no duplicates. -/
theorem graphRootOrder_unique (c : Config arity) : c.graphRootOrder.Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_finRange _).map Sum.inl_injective,
    (EquationGraph.order_unique _).map Sum.inr_injective, ?_⟩
  intro x hx y hy hxy
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hy
  cases hxy

/-- Every interface or equation root is enumerated. -/
theorem graphRootOrder_cover (c : Config arity) (i : c.GraphRoot) :
    i ∈ c.graphRootOrder := by
  cases i with
  | inl i => exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  | inr i =>
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨i, EquationGraph.order_cover _ i, rfl⟩)

/-- Interface roots meet the external boundary, and equation roots meet their opposite side. -/
def graphRootWiring (c : Config arity) : Wiring (Fin c.interface.length ⊕ c.GraphRoot) where
  partner p := match p with
    | .inl i => .inr (.inl i)
    | .inr (.inl i) => .inl i
    | .inr (.inr (.inl i)) => .inr (.inr (.inr i))
    | .inr (.inr (.inr i)) => .inr (.inr (.inl i))
  involutive p := by rcases p with i | (i | (i | i)) <;> rfl
  fixedPointFree p h := by rcases p with i | (i | (i | i)) <;> cases h

/-- Named leaf occurrences retain their root and internal term positions. -/
abbrev GraphLeaf (c : Config arity) := Σ i, (c.graphFragments i).Leaf

/-- Every leaf has an explicit finite index inherited from its term fragment. -/
@[instance_reducible] def graphLeafEnum (c : Config arity) : FinEnum c.GraphLeaf := sigmaEnum

/-- Use structural occurrence indices for this configuration's leaf matching. -/
local instance (c : Config arity) : FinEnum c.GraphLeaf := c.graphLeafEnum

/-- The name written at a configuration's graph leaf. -/
def graphLeafName (c : Config arity) (p : c.GraphLeaf) : ℕ :=
  (c.graphFragments p.1).name p.2

/-- The graph forest's leaf occurrences in syntax order. -/
def graphLeafOrder (c : Config arity) : List c.GraphLeaf :=
  TermFragment.forestOrder c.graphRootOrder c.graphFragments

/-- The graph forest and textual configuration have identical wire-name multiplicities. -/
theorem graphLeaf_count (c : Config arity) (x : ℕ) :
    (c.graphLeafOrder.map c.graphLeafName).count x = c.names.count x := by
  change ((TermFragment.forestOrder c.graphRootOrder c.graphFragments).map
    (fun p ↦ (c.graphFragments p.1).name p.2)).count x = _
  rw [TermFragment.forestOrder_names]
  simp only [graphRootOrder, List.flatMap_append, List.flatMap_map, graphFragments,
    Sum.elim_inl, Sum.elim_inr, Term.fragment_names, List.count_append]
  have hi : (List.finRange c.interface.length).map c.interface.get = c.interface := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  have hn : (List.finRange c.interface.length).flatMap
      (fun i ↦ (c.interface.get i).names) = c.interface.flatMap Term.names := by
    simpa only [List.flatMap_map] using congrArg (fun l ↦ l.flatMap Term.names) hi
  rw [hn]
  have he := EquationGraph.leaf_count c.equations x
  change ((TermFragment.forestOrder (EquationGraph.order c.equations)
    (EquationGraph.fragments c.equations)).map
      (fun p ↦ (EquationGraph.fragments c.equations p.1).name p.2)).count x = _ at he
  rw [TermFragment.forestOrder_names] at he
  rw [he]
  exact (List.count_append (l₁ := c.interface.flatMap Term.names)
    (l₂ := c.equations.flatMap fun e ↦ e.1.names ++ e.2.names)).symm

/-- A closed configuration has exactly two graph endpoints at every used leaf name. -/
theorem graphLeaf_two (c : Config arity) (closed : c.Closed) (p : c.GraphLeaf) :
    (c.graphLeafOrder.map c.graphLeafName).count (c.graphLeafName p) = 2 := by
  have hm : c.graphLeafName p ∈ c.graphLeafOrder.map c.graphLeafName :=
    List.mem_map.mpr ⟨p,
      TermFragment.forestOrder_cover _ c.graphRootOrder_cover c.graphFragments p, rfl⟩
  have hp := List.count_pos_iff.mpr hm
  rw [c.graphLeaf_count] at hp ⊢
  exact closed _ (List.count_pos_iff.mp hp)

/-- Pair equally named leaf occurrences of a closed configuration. -/
def graphLeafWiring (c : Config arity) (closed : c.Closed) : Wiring c.GraphLeaf :=
  Wiring.ofNames c.graphLeafOrder
    (TermFragment.forestOrder_unique _ c.graphRootOrder_unique c.graphFragments)
    (TermFragment.forestOrder_cover _ c.graphRootOrder_cover c.graphFragments)
    c.graphLeafName (c.graphLeaf_two closed)

/-- Compile every cell, equation and interface term of a closed configuration to a finite graph. -/
def toFiniteNet (c : Config arity) (closed : c.Closed) : FiniteNet arity c.interface.length :=
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let leaves := (c.graphLeafWiring closed).map (PortNet.emptyCellEquiv _).symm
  let body := (TermFragment.assemble c.graphFragments c.graphRootWiring leaves).reboundary
    ((Equiv.sumComm _ (Fin 0)).trans (PortNet.emptyCellEquiv _))
  ⟨FinEnum.card (Σ i, (c.graphFragments i).Cell),
    fun p ↦ (c.graphFragments (FinEnum.equiv.symm p).1).label (FinEnum.equiv.symm p).2,
    body.indexed⟩

end Geb.InteractionNet.Config

end
