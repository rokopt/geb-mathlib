/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleLeafPartition
public import Geb.Prototypes.InteractionNet.CouplingIdentity
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Internal wires of a linear rule

Every external port is paired with its unique boundary occurrence. Internal occurrences
pair only with other occurrences of the same internal name. Separating these components
presents the rule's leaf matching as an identity boundary and an internal matching.

## Main definitions

* {lit}`Rule.internalWiring` — the matching between internal rule occurrences.
* {lit}`Rule.leafEndpointPartitionEquiv` — separate external wires from internal endpoints.

## Main statements

* {lit}`Rule.leafWiring_partition` — the rule matching splits into its two components.

## Tags

interaction net, rule, linearity, internal wire, boundary, matching
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Rule

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- Following an internal rule wire finds another internal occurrence. -/
def internalPartner (r : Rule arity a b) (linear : r.Linear) (q : r.InternalLeaf) :
    r.InternalLeaf :=
  match he : (r.leafWiring linear).partner (.inr q.val) with
  | .inl p => by
    have hn := r.leafWiring_partner_name linear (.inr q.val)
    rw [he] at hn
    have h := q.property
    change (EquationGraph.leafName r.equations q.val).isRight at h
    change Sum.inl p = EquationGraph.leafName r.equations q.val at hn
    rw [← hn] at h
    exact (Bool.noConfusion h)
  | .inr p => by
    refine ⟨p, ?_⟩
    have hn := r.leafWiring_partner_name linear (.inr q.val)
    rw [he] at hn
    change EquationGraph.leafName r.equations p = EquationGraph.leafName r.equations q.val at hn
    rw [hn]
    exact q.property

/-- The internal partner is precisely the other endpoint selected by the full rule matching. -/
theorem internalPartner_eq (r : Rule arity a b) (linear : r.Linear) (q : r.InternalLeaf) :
    (r.leafWiring linear).partner (.inr q.val) = .inr (r.internalPartner linear q).val := by
  unfold internalPartner
  split
  · rename_i p hp
    have hn := r.leafWiring_partner_name linear (.inr q.val)
    rw [hp] at hn
    have h := q.property
    change Sum.inl p = EquationGraph.leafName r.equations q.val at hn
    rw [← hn] at h
    cases h
  · rename_i p hp
    exact hp

/-- Following an internal wire twice returns the same occurrence. -/
theorem internalPartner_involutive (r : Rule arity a b) (linear : r.Linear) :
    Function.Involutive (r.internalPartner linear) := by
  intro q
  apply Subtype.ext
  apply Sum.inr_injective (α := Boundary arity a b)
  have h := congrArg (r.leafWiring linear).partner (r.internalPartner_eq linear q)
  rw [Wiring.partner_partner, internalPartner_eq] at h
  exact h.symm

/-- Internal wire endpoints remain distinct. -/
theorem internalPartner_ne (r : Rule arity a b) (linear : r.Linear) (q : r.InternalLeaf) :
    r.internalPartner linear q ≠ q := by
  intro h
  have he := r.internalPartner_eq linear q
  rw [h] at he
  exact (r.leafWiring linear).fixedPointFree (.inr q.val) he

/-- Restrict the rule matching to its internal wire occurrences. -/
def internalWiring (r : Rule arity a b) (linear : r.Linear) : Wiring r.InternalLeaf where
  partner := r.internalPartner linear
  involutive := r.internalPartner_involutive linear
  fixedPointFree := r.internalPartner_ne linear

/-- The internal matching joins occurrences bearing the same internal wire name. -/
theorem internalWiring_name (r : Rule arity a b) (linear : r.Linear) (q : r.InternalLeaf) :
    r.internalLeafName ((r.internalWiring linear).partner q) = r.internalLeafName q := by
  have h := r.leafWiring_partner_name linear (.inr q.val)
  rw [r.internalPartner_eq linear q] at h
  change EquationGraph.leafName r.equations (r.internalPartner linear q).val =
    EquationGraph.leafName r.equations q.val at h
  rw [r.internalLeafName_eq, r.internalLeafName_eq] at h
  exact Sum.inr.inj h

/-- Separate the two endpoint copies of the external boundary from internal occurrences. -/
def leafEndpointPartitionEquiv (r : Rule arity a b) (linear : r.Linear) :
    r.LeafEndpoint ≃ (Boundary arity a b ⊕ Boundary arity a b) ⊕ r.InternalLeaf :=
  (Equiv.sumCongr (Equiv.refl _) (r.leafPartitionEquiv linear)).trans (Equiv.sumAssoc _ _ _).symm

/-- The leaf matching consists of the external identity wires and the internal matching. -/
theorem leafWiring_partition (r : Rule arity a b) (linear : r.Linear) :
    (r.leafWiring linear).map (r.leafEndpointPartitionEquiv linear) =
      (Wiring.identityBoundary (Boundary arity a b)).sum (r.internalWiring linear) := by
  let e := r.leafEndpointPartitionEquiv linear
  have h : Wiring.Respects e.symm.toEmbedding
      ((Wiring.identityBoundary (Boundary arity a b)).sum (r.internalWiring linear))
      (r.leafWiring linear) := by
    rintro ((p | p) | q)
    · exact r.leafWiring_boundary_partner linear p (r.boundaryOccurrence linear p).val
        (r.boundaryOccurrence linear p).property
    · exact ((r.leafWiring linear).partner_eq_iff.mp
        (r.leafWiring_boundary_partner linear p (r.boundaryOccurrence linear p).val
          (r.boundaryOccurrence linear p).property)).symm
    · exact r.internalPartner_eq linear q
  have he := h.map_eq (Wiring.respects_refl _) e.symm (fun _ ↦ rfl)
  rw [← he]
  exact Wiring.map_symm_map e.symm _

end Geb.InteractionNet.Rule

end
