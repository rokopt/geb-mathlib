/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigInteractionEmbedding
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Textual instantiation and graph joining have the same forest

The two constructions embed into the same matching after their argument cuts. The cell
and boundary allocation bijections identify their surviving endpoints there. Consequently
the complete forests agree, including any closed wires created by attachment.

## Main definitions

* {lit}`Config.interactionForestEndpointsEquiv` — corresponding surviving endpoints of the forests.

## Main statements

* {lit}`Config.interactionForest_wiring` — attachment and joining preserve the same wires.
* {lit}`Config.interactionForest_loops` — both constructions retain the same closed wires.

## Tags

interaction net, compiler, instantiation, graph, joining, forest
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- Identify the forest endpoints by the cell and boundary allocation bijections. -/
def interactionForestEndpointsEquiv (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (next : ℕ) (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  endpointEquiv arity (c.interactionForestBoundaryEquiv r linear next xs ys)
    (c.interactionForestCellsEquiv r linear next xs ys)
    (c.interactionForestCellsEquiv_label r linear next xs ys)

/-- Corresponding live endpoints occupy the same positions in the common matching. -/
theorem interactionForest_endpoint_agreement (c : Config arity) (r : Rule arity a b)
    (linear : r.Linear) (next : ℕ) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) (p) :
    c.interactionAttachedEmbedding r linear next xs ys p =
      c.interactionJoinedEmbedding r linear xs ys
        (c.interactionForestEndpointsEquiv r linear next xs ys p) := by
  rcases p with (⟨i, u | ⟨q, p⟩⟩ | p) | ⟨⟨i, d | ⟨q, d⟩⟩ | d, v⟩
  · exact congrArg Sum.inl (r.internalRelocate_root linear xs ys i).symm
  · dsimp only [Rule.instantiationFragments] at p ⊢
    change Sum.inl (Sum.inr (r.replacementEndpointsEquiv linear next xs ys
      ⟨⟨i, q⟩, .inl (.inr p)⟩)) = _
    simp only [interactionForestEndpointsEquiv, endpointEquiv_boundary,
      interactionForestBoundaryEquiv, Rule.attachedBoundarySplit, Equiv.trans_apply,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.coe_fn_mk,
      Rule.instantiationFragments]
    erw [r.replacementEndpointsEquiv_leaf linear next xs ys]
    cases he : r.replacementLeavesEquiv linear next xs ys ⟨⟨i, q⟩, p⟩ with
    | inl p =>
      exact congrArg Sum.inl
        (r.internalRelocate_argument linear xs ys ⟨p.1, .inl (.inr p.2)⟩).symm
    | inr q => exact congrArg Sum.inl (r.internalRelocate_leaf linear xs ys q).symm
  · rfl
  · exact congrArg Sum.inl (r.internalRelocate_cell linear xs ys i ⟨d, v⟩).symm
  · change Sum.inl (Sum.inr (r.replacementEndpointsEquiv linear next xs ys
      ⟨⟨i, q⟩, .inr ⟨d, v⟩⟩)) = _
    erw [r.replacementEndpointsEquiv_cell linear next xs ys]
    exact congrArg Sum.inl (r.internalRelocate_argument linear xs ys _).symm
  · rfl

/-- Textual attachment and graph joining identify every wire under the allocation bijections. -/
theorem interactionForest_wiring (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (next : ℕ) (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (c.interactionAttachedForest r next xs ys).wiring.map
      (c.interactionForestEndpointsEquiv r linear next xs ys) =
        (c.interactionJoinedForest r linear xs ys).wiring :=
  (c.interactionAttached_spec r linear next xs ys).1.map_eq
    (c.interactionJoined_spec r linear xs ys).1 _
      (c.interactionForest_endpoint_agreement r linear next xs ys)

/-- Textual attachment and graph joining create the same number of closed wires. -/
theorem interactionForest_loops (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (next : ℕ) (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (c.interactionAttachedForest r next xs ys).loops =
      (c.interactionJoinedForest r linear xs ys).loops :=
  (c.interactionAttached_spec r linear next xs ys).2.trans
    (c.interactionJoined_spec r linear xs ys).2.symm

end Geb.InteractionNet.Config

end
