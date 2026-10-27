/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleGraph
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Boundary occurrences in linear rule graphs

Each external port of a linear rule is matched to its unique variable occurrence in the
rule's equation forest. Following that named wire selects the occurrence constructively.
Different external ports select different leaves; no internal wire occurrence is selected.
These facts identify the occurrence at which each auxiliary argument is attached during
rule instantiation.

## Main definitions

* {lit}`Rule.boundaryOccurrence` — the unique forest leaf named by a boundary port.

## Main statements

* {lit}`Rule.boundaryOccurrence_unique` — the selected leaf is unique at that boundary name.
* {lit}`Rule.boundaryOccurrence_injective` — distinct ports select distinct occurrences.

## Tags

interaction net, rule, linearity, boundary, occurrence, instantiation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Rule

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- A forest leaf named by an external port is the other end of that port's named wire. -/
theorem leafWiring_boundary_partner (r : Rule arity a b) (linear : r.Linear)
    (p : Boundary arity a b) (q : EquationGraph.Leaf r.equations)
    (name : EquationGraph.leafName r.equations q = .inl p) :
    (r.leafWiring linear).partner (.inl p) = .inr q := by
  unfold leafWiring
  apply Wiring.ofNames_partner_eq
  · intro h
    cases h
  · exact name

/-- The compiled rule matching joins endpoints with the same declared wire name. -/
theorem leafWiring_partner_name (r : Rule arity a b) (linear : r.Linear)
    (p : r.LeafEndpoint) :
    r.leafEndpointName ((r.leafWiring linear).partner p) = r.leafEndpointName p := by
  unfold leafWiring
  apply Wiring.ofNames_partner_name

/-- Following an external port's named wire finds its corresponding variable occurrence. -/
def boundaryOccurrence (r : Rule arity a b) (linear : r.Linear) (p : Boundary arity a b) :
    {q : EquationGraph.Leaf r.equations // EquationGraph.leafName r.equations q = .inl p} := by
  have hn := r.leafWiring_partner_name linear (.inl p)
  change r.leafEndpointName ((r.leafWiring linear).partner (.inl p)) = .inl p at hn
  cases he : (r.leafWiring linear).partner (.inl p) with
  | inl q =>
    have hq : q = p := Sum.inl.inj (he ▸ hn)
    exact ((r.leafWiring linear).fixedPointFree (.inl p)
      (he.trans (congrArg Sum.inl hq))).elim
  | inr q =>
    refine ⟨q, ?_⟩
    change r.leafEndpointName (.inr q) = .inl p
    exact he ▸ hn

/-- Linearity identifies every leaf with a given external name with its selected occurrence. -/
theorem boundaryOccurrence_unique (r : Rule arity a b) (linear : r.Linear)
    (p : Boundary arity a b) (q : EquationGraph.Leaf r.equations)
    (name : EquationGraph.leafName r.equations q = .inl p) :
    q = (r.boundaryOccurrence linear p).val := by
  have hq := r.leafWiring_boundary_partner linear p q name
  have hp := r.leafWiring_boundary_partner linear p (r.boundaryOccurrence linear p).val
    (r.boundaryOccurrence linear p).property
  exact Sum.inr.inj (hq.symm.trans hp)

/-- No two external ports select the same variable occurrence in the replacement forest. -/
theorem boundaryOccurrence_injective (r : Rule arity a b) (linear : r.Linear) :
    Function.Injective (fun p ↦ (r.boundaryOccurrence linear p).val) := by
  intro p q h
  have hn := congrArg (EquationGraph.leafName r.equations) h
  rw [(r.boundaryOccurrence linear p).property, (r.boundaryOccurrence linear q).property] at hn
  exact Sum.inl.inj hn

end Geb.InteractionNet.Rule

end
