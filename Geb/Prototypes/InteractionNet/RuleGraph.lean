/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Calculus
public import Geb.Prototypes.InteractionNet.EquationGraph
public import Geb.Prototypes.InteractionNet.NamedWiring
public import Geb.Prototypes.InteractionNet.PortSystem
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Compiling linear textual rules to finite graphs

A linear rule uses each boundary name once and each internal name twice. Adding one
external endpoint for each boundary name therefore gives exactly two occurrences of every
wire name. These pairs connect the equation forest into a graph rule. The construction
accepts arbitrary nested terms and retains closed wires produced during assembly.

## Main definitions

* {lit}`Rule.leafWiring` — connect named occurrences and external rule ports.
* {lit}`Rule.toPortRule` — compile a linear textual rule to a finite graph replacement.
* {lit}`System.toPortSystem` — compile an oriented system of linear rules.

## Main statements

* {lit}`Rule.leafEndpoints_count` — every wire has exactly two endpoints after adding the boundary.
* {lit}`System.toPortSystem_rule` — successful textual lookup selects the compiled rule body.

## Tags

interaction net, compiler, rule, linearity, graph, boundary
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

namespace Rule

variable {a b : α}

/-- The external boundary followed by all equation-leaf occurrences. -/
abbrev LeafEndpoint (r : Rule arity a b) := Boundary arity a b ⊕ EquationGraph.Leaf r.equations

/-- Leaf endpoints have a constructive enumeration inherited from their term positions. -/
@[instance_reducible] def leafEndpointEnum (r : Rule arity a b) : FinEnum r.LeafEndpoint :=
  let := sigmaEnum (C := fun i ↦ (EquationGraph.fragments r.equations i).Leaf)
  inferInstance

/-- Use the occurrence enumeration when assembling this rule's named wires. -/
local instance (r : Rule arity a b) : FinEnum r.LeafEndpoint := r.leafEndpointEnum

/-- The name on an external rule endpoint or a term's leaf occurrence. -/
def leafEndpointName (r : Rule arity a b) : r.LeafEndpoint → Boundary arity a b ⊕ Fin r.fresh :=
  Sum.elim Sum.inl (EquationGraph.leafName r.equations)

/-- Enumerate the external endpoints first, then the equation forest's leaves. -/
def leafEndpoints (r : Rule arity a b) : List r.LeafEndpoint :=
  (FinEnum.toList (Boundary arity a b)).map Sum.inl ++
    (EquationGraph.leafOrder r.equations).map Sum.inr

/-- External and internal occurrence positions are distinct and individually unique. -/
theorem leafEndpoints_unique (r : Rule arity a b) : r.leafEndpoints.Nodup := by
  apply List.nodup_append.mpr
  refine ⟨FinEnum.nodup_toList.map Sum.inl_injective,
    (TermFragment.forestOrder_unique _ (EquationGraph.order_unique _) _).map
      Sum.inr_injective, ?_⟩
  intro x hx y hy hxy
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hy
  cases hxy

/-- Every external endpoint and equation-leaf occurrence appears in the enumeration. -/
theorem leafEndpoints_cover (r : Rule arity a b) (p : r.LeafEndpoint) :
    p ∈ r.leafEndpoints := by
  cases p with
  | inl p => exact List.mem_append_left _ (List.mem_map.mpr ⟨p, FinEnum.mem_toList p, rfl⟩)
  | inr p =>
    exact List.mem_append_right _ (List.mem_map.mpr
      ⟨p, TermFragment.forestOrder_cover _ (EquationGraph.order_cover _) _ p, rfl⟩)

/-- Linearity makes every wire name occur twice after adjoining the external boundary. -/
theorem leafEndpoints_count (r : Rule arity a b) (linear : r.Linear)
    (x : Boundary arity a b ⊕ Fin r.fresh) :
    (r.leafEndpoints.map r.leafEndpointName).count x = 2 := by
  simp only [leafEndpoints, List.map_append, List.map_map, leafEndpointName,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, List.count_append]
  rw [EquationGraph.leaf_count]
  change ((FinEnum.toList (Boundary arity a b)).map Sum.inl).count x + r.names.count x = 2
  cases x with
  | inl i =>
    rw [List.count_map_of_injective _ Sum.inl Sum.inl_injective,
      FinEnum.nodup_toList.count, linear.1]
    simp only [FinEnum.mem_toList, ↓reduceIte]
  | inr i =>
    have hn : Sum.inr i ∉ (FinEnum.toList (Boundary arity a b)).map
        (Sum.inl : Boundary arity a b → Boundary arity a b ⊕ Fin r.fresh) := by
      intro h
      obtain ⟨j, _, h⟩ := List.mem_map.mp h
      cases h
    rw [List.count_eq_zero_of_not_mem hn, linear.2]

/-- Join every equation occurrence to the other endpoint with its wire name. -/
def leafWiring (r : Rule arity a b) (linear : r.Linear) : Wiring r.LeafEndpoint :=
  Wiring.ofNames r.leafEndpoints r.leafEndpoints_unique r.leafEndpoints_cover
    r.leafEndpointName (fun p ↦ r.leafEndpoints_count linear (r.leafEndpointName p))

/-- Assemble and index a linear rule's replacement graph. -/
def toPortRule (r : Rule arity a b) (linear : r.Linear) : PortRule arity a b :=
  let f := EquationGraph.fragments r.equations
  let := sigmaEnum (C := fun i ↦ (f i).Cell)
  let roots := (EquationGraph.rootWiring r.equations).map (PortNet.emptyCellEquiv _).symm
  let body := (TermFragment.assemble f roots (r.leafWiring linear)).reboundary
    (PortNet.emptyCellEquiv (Boundary arity a b))
  ⟨FinEnum.card (Σ i, (f i).Cell),
    fun c ↦ (f (FinEnum.equiv.symm c).1).label (FinEnum.equiv.symm c).2, body.indexed⟩

end Rule

namespace System

/-- Every registered textual replacement obeys the rule boundary's linearity invariant. -/
def Linear (s : System arity) : Prop := ∀ a b r, s.rule a b = some r → r.Linear

/-- A textual system registers at most one orientation of any interacting symbol pair. -/
def Oriented (s : System arity) : Prop := ∀ a b r, s.rule a b = some r → s.rule b a = none

/-- Compile each successful rule lookup, using linearity to assemble its named wires. -/
def graphRule (s : System arity) (linear : s.Linear) (a b : α) : Option (PortRule arity a b) :=
  match h : s.rule a b with
  | none => none
  | some r => some (r.toPortRule (linear a b r h))

/-- Translating a system preserves its unique permitted orientation. -/
def toPortSystem (s : System arity) (linear : s.Linear) (oriented : s.Oriented) :
    PortSystem arity where
  rule := s.graphRule linear
  oriented a b r h := by
    change (∀ a b r, s.rule a b = some r → r.Linear) at linear
    change (∀ a b r, s.rule a b = some r → s.rule b a = none) at oriented
    unfold graphRule at h
    split at h
    · cases h
    · rename_i body hb
      have hn := oriented a b body hb
      unfold graphRule
      split
      · rfl
      · rename_i body' hb'
        cases hb'.symm.trans hn

/-- A successful textual rule lookup selects exactly its compiled replacement graph. -/
theorem toPortSystem_rule (s : System arity) (linear : s.Linear) (oriented : s.Oriented)
    {a b : α} {r : Rule arity a b} (h : s.rule a b = some r) :
    (s.toPortSystem linear oriented).rule a b = some (r.toPortRule (linear a b r h)) := by
  change (∀ a b r, s.rule a b = some r → r.Linear) at linear
  change s.graphRule linear a b = _
  unfold graphRule
  split
  · rename_i hn
    cases hn.symm.trans h
  · rename_i r' hr'
    have he : r' = r := Option.some.inj (hr'.symm.trans h)
    subst r'
    rfl

end System

end Geb.InteractionNet

end
