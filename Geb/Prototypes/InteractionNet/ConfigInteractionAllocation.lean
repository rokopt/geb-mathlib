/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigAgentPairForest
public import Geb.Prototypes.InteractionNet.ForestAttachmentContext
public import Geb.Prototypes.InteractionNet.RuleInstantiationAllocation
public import Geb.Prototypes.InteractionNet.RuleOpenForest
public import Geb.Prototypes.InteractionNet.BoundaryJoin
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Comparing the allocations on the two sides of interaction

The textual result keeps the rule's original cells, inserts the argument cells and retains
the surrounding configuration. Joining the argument context to the open rule forest has
the same allocation in a different order. The boundary correspondence separates argument
and context positions from the equation roots and internal occurrences closed by the rule.

## Main definitions

* {lit}`Config.interactionAttachedForest` — the substituted replacement forest beside the context.
* {lit}`Config.interactionJoinedForest` — the argument context joined to the open rule forest.
* {lit}`Config.interactionForestCellsEquiv` — the cell correspondence between those allocations.
* {lit}`Config.interactionForestBoundaryEquiv` — the corresponding exposed boundary positions.

## Main statements

* {lit}`Config.interactionForestCellsEquiv_label` — the allocation correspondence preserves symbols.

## Tags

interaction net, compiler, interaction, allocation, cell, boundary, join
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

namespace Rule

/-- Separate the attached rule forest's original cells from its argument cells. -/
def attachedCellsEquiv (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Σ i, ((EquationGraph.fragments r.equations i).attach
      (r.instantiationFragments next xs ys i)).Cell) ≃
        (Σ i, (EquationGraph.fragments r.equations i).Cell) ⊕
          (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Cell) :=
  (Equiv.sigmaSumDistrib (fun i ↦ (EquationGraph.fragments r.equations i).Cell)
    (fun i ↦ Σ q, (r.instantiationFragments next xs ys i q).Cell)).trans
      (Equiv.sumCongr (Equiv.refl _) ((Equiv.sigmaAssoc
        (fun i q ↦ (r.instantiationFragments next xs ys i q).Cell)).symm.trans
          (r.replacementCellsEquiv linear next xs ys)))

/-- Separate old roots from all replacement leaves in the attached rule forest. -/
def attachedBoundarySplit (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    TermFragment.AttachedForestBoundary (EquationGraph.fragments r.equations)
      (r.instantiationFragments next xs ys) ≃
        EquationGraph.Root r.equations ⊕ (Σ q : EquationGraph.Leaf r.equations,
          (r.instantiationFragments next xs ys q.1 q.2).Leaf) where
  toFun p := match p with
    | ⟨i, .inl _⟩ => .inl i
    | ⟨i, .inr ⟨q, p⟩⟩ => .inr ⟨⟨i, q⟩, p⟩
  invFun p := match p with
    | .inl i => ⟨i, .inl ()⟩
    | .inr ⟨⟨i, q⟩, p⟩ => ⟨i, .inr ⟨q, p⟩⟩
  left_inv p := by rcases p with ⟨i, u | ⟨q, p⟩⟩ <;> rfl
  right_inv p := by rcases p with i | ⟨⟨i, q⟩, p⟩ <;> rfl

end Rule

namespace Config

/-- The attached replacement forest beside the untouched configuration forest. -/
def interactionAttachedForest (c : Config arity) (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  (PortNet.sigma (fun i ↦ ((EquationGraph.fragments r.equations i).attach
    (r.instantiationFragments next xs ys i)).net)).sum c.graphForest

/-- Join the argument context to the rule forest before closing the rule's internal positions. -/
def interactionJoinedForest (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    PortNet arity (Sum.elim (c.agentPairLabel xs ys)
      (fun p : Σ i, (EquationGraph.fragments r.equations i).Cell ↦
        (EquationGraph.fragments r.equations p.1).label p.2))
          (c.AgentPairBoundary xs ys ⊕ r.ClosedBoundary) :=
  let : DecidableEq (c.AgentPairCell xs ys) := (c.agentPairCellEnum xs ys).decEq
  let : DecidableEq (c.AgentPairBoundary xs ys) := (c.agentPairBoundaryEnum xs ys).decEq
  let : DecidableEq (Σ i, (EquationGraph.fragments r.equations i).Cell) := sigmaEnum.decEq
  let : DecidableEq r.ClosedBoundary := r.closedBoundaryEnum.decEq
  (c.agentPairBody xs ys).join (r.openForest linear) (FinEnum.toList _)
    FinEnum.nodup_toList FinEnum.mem_toList

/-- Reorder retained rule, argument and context cells to the allocation made by graph joining. -/
def interactionForestCellsEquiv (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (next : ℕ) (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Σ i, ((EquationGraph.fragments r.equations i).attach
      (r.instantiationFragments next xs ys i)).Cell) ⊕ c.GraphCell ≃
        c.AgentPairCell xs ys ⊕ (Σ i, (EquationGraph.fragments r.equations i).Cell) :=
  let e : ((Σ i, (EquationGraph.fragments r.equations i).Cell) ⊕
      (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Cell)) ⊕ c.GraphCell ≃
        c.AgentPairCell xs ys ⊕ (Σ i, (EquationGraph.fragments r.equations i).Cell) :=
    (Equiv.sumAssoc _ _ _).trans (Equiv.sumComm _ _)
  (Equiv.sumCongr (r.attachedCellsEquiv linear next xs ys) (Equiv.refl _)).trans e

/-- The reordered allocation keeps the original symbol of every retained or inserted cell. -/
theorem interactionForestCellsEquiv_label (c : Config arity) (r : Rule arity a b)
    (linear : r.Linear) (next : ℕ) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ)
    (p : (Σ i, ((EquationGraph.fragments r.equations i).attach
      (r.instantiationFragments next xs ys i)).Cell) ⊕ c.GraphCell) :
    Sum.elim (c.agentPairLabel xs ys)
      (fun p : Σ i, (EquationGraph.fragments r.equations i).Cell ↦
        (EquationGraph.fragments r.equations p.1).label p.2)
      (c.interactionForestCellsEquiv r linear next xs ys p) =
        Sum.elim (TermFragment.attachedForestLabel (EquationGraph.fragments r.equations)
          (r.instantiationFragments next xs ys)) c.graphLabel p := by
  rcases p with ⟨i, p | ⟨q, p⟩⟩ | p
  · rfl
  · exact r.replacementCellsEquiv_label linear next xs ys ⟨⟨i, q⟩, p⟩
  · rfl

/-- Match argument and context positions with the rule's remaining roots and internal leaves. -/
def interactionForestBoundaryEquiv (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (next : ℕ) (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    TermFragment.AttachedForestBoundary (EquationGraph.fragments r.equations)
      (r.instantiationFragments next xs ys) ⊕ c.GraphForestBoundary ≃
        c.AgentPairBoundary xs ys ⊕ r.ClosedBoundary :=
  let e : (EquationGraph.Root r.equations ⊕
      ((Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf) ⊕ r.InternalLeaf)) ⊕
        c.GraphForestBoundary ≃ c.AgentPairBoundary xs ys ⊕ r.ClosedBoundary :=
    { toFun := fun p ↦ match p with
        | .inl (.inl i) => .inr (.inl i)
        | .inl (.inr (.inl p)) => .inl (.inl p)
        | .inl (.inr (.inr q)) => .inr (.inr q)
        | .inr p => .inl (.inr p)
      invFun := fun p ↦ match p with
        | .inr (.inl i) => .inl (.inl i)
        | .inl (.inl p) => .inl (.inr (.inl p))
        | .inr (.inr q) => .inl (.inr (.inr q))
        | .inl (.inr p) => .inr p
      left_inv := by rintro ((i | (p | q)) | p) <;> rfl
      right_inv := by rintro ((p | p) | (i | q)) <;> rfl }
  (Equiv.sumCongr ((r.attachedBoundarySplit next xs ys).trans
    (Equiv.sumCongr (Equiv.refl _) (r.replacementLeavesEquiv linear next xs ys)))
      (Equiv.refl _)).trans e

end Config

end Geb.InteractionNet

end
