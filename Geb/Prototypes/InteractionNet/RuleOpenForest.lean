/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleInternalWiring
public import Geb.Prototypes.InteractionNet.PartialClosureIdentity
public import Geb.Prototypes.InteractionNet.AssemblyIso
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# A rule forest with its external occurrences exposed

Each external port of a linear rule names exactly one leaf in its equation forest.
Expose those leaf occurrences directly, then close the equation roots and internal leaves.
The result is isomorphic to the compiled rule graph: the ordinary compilation only adds
identity wires between its external ports and these same occurrences.

## Main definitions

* {lit}`Rule.openForest` — expose boundary occurrences directly in the rule forest.

## Main statements

* {lit}`Rule.openForestIso` — closing the remaining roots and leaves gives the compiled rule.

## Tags

interaction net, compiler, rule, forest, boundary, partial closure
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Rule

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- Every boundary position of the rule's unassembled equation forest. -/
abbrev ForestBoundary (r : Rule arity a b) :=
  Σ i, Unit ⊕ (EquationGraph.fragments r.equations i).Leaf

/-- The equation roots and internal leaves that must be closed after exposing external leaves. -/
abbrev ClosedBoundary (r : Rule arity a b) := EquationGraph.Root r.equations ⊕ r.InternalLeaf

/-- Enumerate the boundary positions that the rule closes internally. -/
@[instance_reducible] def closedBoundaryEnum (r : Rule arity a b) : FinEnum r.ClosedBoundary :=
  let := r.internalLeafEnum
  inferInstance

/-- Separate each root from its named leaf occurrences before partitioning the leaves. -/
def forestBoundarySplit (r : Rule arity a b) :
    r.ForestBoundary ≃ EquationGraph.Root r.equations ⊕ EquationGraph.Leaf r.equations where
  toFun p := match p with
    | ⟨i, .inl _⟩ => .inl i
    | ⟨i, .inr q⟩ => .inr ⟨i, q⟩
  invFun p := match p with
    | .inl i => ⟨i, .inl ()⟩
    | .inr ⟨i, q⟩ => ⟨i, .inr q⟩
  left_inv p := by rcases p with ⟨i, u | q⟩ <;> rfl
  right_inv p := by rcases p with i | ⟨i, q⟩ <;> rfl

/-- Move the unique external leaf occurrences before the positions closed by the rule. -/
def openBoundaryEquiv (r : Rule arity a b) (linear : r.Linear) :
    r.ForestBoundary ≃ Boundary arity a b ⊕ r.ClosedBoundary :=
  let swap : EquationGraph.Root r.equations ⊕ (Boundary arity a b ⊕ r.InternalLeaf) ≃
      Boundary arity a b ⊕ r.ClosedBoundary :=
    { toFun := fun p ↦ match p with
        | .inl i => .inr (.inl i)
        | .inr (.inl p) => .inl p
        | .inr (.inr q) => .inr (.inr q)
      invFun := fun p ↦ match p with
        | .inl p => .inr (.inl p)
        | .inr (.inl i) => .inl i
        | .inr (.inr q) => .inr (.inr q)
      left_inv := by rintro (i | (p | q)) <;> rfl
      right_inv := by rintro (p | (i | q)) <;> rfl }
  (r.forestBoundarySplit.trans (Equiv.sumCongr (Equiv.refl _)
    (r.leafPartitionEquiv linear))).trans swap

/-- The rule forest with its external leaf occurrences directly exposed. -/
def openForest (r : Rule arity a b) (linear : r.Linear) :
    PortNet arity (fun c : Σ i, (EquationGraph.fragments r.equations i).Cell ↦
      (EquationGraph.fragments r.equations c.1).label c.2)
        (Boundary arity a b ⊕ r.ClosedBoundary) :=
  (PortNet.sigma (fun i ↦ (EquationGraph.fragments r.equations i).net)).reboundary
    (r.openBoundaryEquiv linear)

/-- Close the equation roots and the internal rule wires in their separate blocks. -/
def closedWiring (r : Rule arity a b) (linear : r.Linear) : Wiring r.ClosedBoundary :=
  (EquationGraph.rootWiring r.equations).sum (r.internalWiring linear)

/-- The matching used by ordinary rule compilation, including its external identity wires. -/
def graphContextWiring (r : Rule arity a b) (linear : r.Linear) :
    Wiring (Boundary arity a b ⊕ r.ForestBoundary) :=
  (((EquationGraph.rootWiring r.equations).map (PortNet.emptyCellEquiv _).symm).sum
    (r.leafWiring linear)).map
      ((TermFragment.assemblyBoundaryEquiv (EquationGraph.fragments r.equations)).trans
        (Equiv.sumCongr (PortNet.emptyCellEquiv _) (Equiv.refl _)))

private def contextLeaf (r : Rule arity a b) :
    r.LeafEndpoint ↪ Boundary arity a b ⊕ r.ForestBoundary where
  toFun p := match p with
    | .inl p => .inl p
    | .inr ⟨i, q⟩ => .inr ⟨i, .inr q⟩
  inj' := by
    rintro (p | ⟨i, q⟩) (p' | ⟨i', q'⟩) h
    · exact congrArg Sum.inl (Sum.inl.inj h)
    · cases h
    · cases h
    · have he : i = i' := congrArg Sigma.fst (Sum.inr.inj h)
      subst i'
      have hq := Sum.inr.inj (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2)
      cases hq
      rfl

private theorem contextLeaf_respects (r : Rule arity a b) (linear : r.Linear) :
    Wiring.Respects (contextLeaf r) (r.leafWiring linear) (r.graphContextWiring linear) := by
  let e := (TermFragment.assemblyBoundaryEquiv (R := Fin 0)
    (EquationGraph.fragments r.equations)).trans
      (Equiv.sumCongr (PortNet.emptyCellEquiv (Boundary arity a b)) (Equiv.refl _))
  have h := (Wiring.respects_inr
    ((EquationGraph.rootWiring r.equations).map (PortNet.emptyCellEquiv _).symm)
      (r.leafWiring linear)).trans (Wiring.respects_map e _)
  have he (q : r.LeafEndpoint) : e (.inr q) = contextLeaf r q := by
    rcases q with q | ⟨i, q⟩ <;> rfl
  intro p
  have hp := h p
  change (r.graphContextWiring linear).partner (e (.inr p)) =
    e (.inr ((r.leafWiring linear).partner p)) at hp
  rw [he, he] at hp
  exact hp

/-- The assembled rule context consists of identity wires and the remaining closure matching. -/
theorem graphContextWiring_open (r : Rule arity a b) (linear : r.Linear) :
    (r.graphContextWiring linear).map (Equiv.sumCongr (Equiv.refl _)
      (r.openBoundaryEquiv linear)) = PortNet.partialIdentity (r.closedWiring linear) := by
  let e := Equiv.sumCongr (Equiv.refl (Boundary arity a b)) (r.openBoundaryEquiv linear)
  have h : Wiring.Respects e.symm.toEmbedding (PortNet.partialIdentity (r.closedWiring linear))
      (r.graphContextWiring linear) := by
    rintro (p | (p | (i | q)))
    · exact (contextLeaf_respects r linear (.inl p)).trans
        (congrArg (contextLeaf r) (r.leafWiring_boundary_partner linear p
          (r.boundaryOccurrence linear p).val (r.boundaryOccurrence linear p).property))
    · have h := (contextLeaf_respects r linear (.inl p)).trans
        (congrArg (contextLeaf r) (r.leafWiring_boundary_partner linear p
          (r.boundaryOccurrence linear p).val (r.boundaryOccurrence linear p).property))
      exact ((r.graphContextWiring linear).partner_eq_iff.mp h).symm
    · rfl
    · exact (contextLeaf_respects r linear (.inr q.val)).trans
        (congrArg (contextLeaf r) (r.internalPartner_eq linear q))
  have he := h.map_eq (Wiring.respects_refl _) e.symm (fun _ ↦ rfl)
  rw [← he]
  exact Wiring.map_symm_map e.symm _

/-- Closing the exposed rule forest gives exactly the compiled rule up to cell indexing. -/
def openForestIso (r : Rule arity a b) (linear : r.Linear) :
    let := sigmaEnum (C := fun i ↦ (EquationGraph.fragments r.equations i).Cell)
    let := r.closedBoundaryEnum
    (r.toPortRule linear).2.2.Iso ((r.openForest linear).close (r.closedWiring linear)) := by
  let := sigmaEnum (C := fun i ↦ (EquationGraph.fragments r.equations i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (EquationGraph.fragments r.equations i).Leaf)
  let := r.closedBoundaryEnum
  let f := EquationGraph.fragments r.equations
  let n := PortNet.sigma (fun i ↦ (f i).net)
  let w := r.graphContextWiring linear
  have h := PortNet.coupleIso n (r.openForest linear) w (PortNet.partialIdentity
    (r.closedWiring linear)) (r.openBoundaryEquiv linear) (Equiv.refl _)
      (fun _ ↦ rfl) rfl rfl (r.graphContextWiring_open linear)
  rw [PortNet.couple_partialIdentity] at h
  have he : ((TermFragment.assemble f
      ((EquationGraph.rootWiring r.equations).map (PortNet.emptyCellEquiv _).symm)
        (r.leafWiring linear)).reboundary (PortNet.emptyCellEquiv _)) = n.couple w := by
    dsimp only [TermFragment.assemble]
    rw [← PortNet.couple_reboundary]
    dsimp only [w, graphContextWiring]
    rw [Wiring.map_trans]
  change ((TermFragment.assemble f
    ((EquationGraph.rootWiring r.equations).map (PortNet.emptyCellEquiv _).symm)
      (r.leafWiring linear)).reboundary (PortNet.emptyCellEquiv _)).indexed.Iso _
  rw [he]
  exact (PortNet.indexedIso (n.couple w)).symm.trans h

end Geb.InteractionNet.Rule

end
