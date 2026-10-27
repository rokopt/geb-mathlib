/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleBoundaryOccurrences
public import Geb.Prototypes.InteractionNet.FiniteCells
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Separating rule boundary occurrences from internal wires

Linearity gives one leaf occurrence for each external rule port. Every other occurrence
carries an internal wire name. This partition is a constructive bijection: external ports
select their occurrence by the rule matching, while internal leaves retain their positions.

## Main definitions

* {lit}`Rule.InternalLeaf` — an occurrence of an internal rule name.
* {lit}`Rule.leafPartitionEquiv` — external ports followed by internal occurrences.

## Tags

interaction net, rule, linearity, boundary, occurrence, internal wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Rule

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- A rule leaf whose name denotes an internal wire. -/
abbrev InternalLeaf (r : Rule arity a b) :=
  {q : EquationGraph.Leaf r.equations // (EquationGraph.leafName r.equations q).isRight}

/-- Enumerate internal occurrences by filtering the finite equation-leaf positions. -/
@[instance_reducible] def internalLeafEnum (r : Rule arity a b) : FinEnum r.InternalLeaf :=
  let := sigmaEnum (C := fun i ↦ (EquationGraph.fragments r.equations i).Leaf)
  PortNet.subtypeEnum (fun q ↦ (EquationGraph.leafName r.equations q).isRight)

/-- The internal name at an internal occurrence. -/
def internalLeafName (r : Rule arity a b) (q : r.InternalLeaf) : Fin r.fresh :=
  (EquationGraph.leafName r.equations q.val).getRight q.property

/-- Reading an internal name recovers the occurrence's original sum-valued wire name. -/
theorem internalLeafName_eq (r : Rule arity a b) (q : r.InternalLeaf) :
    EquationGraph.leafName r.equations q.val = .inr (r.internalLeafName q) :=
  Sum.eq_right_getRight_of_isRight q.property

/-- Classify a rule occurrence by its external port or its retained internal position. -/
def leafPartition (r : Rule arity a b) (q : EquationGraph.Leaf r.equations) :
    Boundary arity a b ⊕ r.InternalLeaf :=
  match hn : EquationGraph.leafName r.equations q with
  | .inl p => .inl p
  | .inr _ => .inr ⟨q, by rw [hn]; rfl⟩

/-- An externally named leaf is classified by that port. -/
theorem leafPartition_boundary (r : Rule arity a b) (q : EquationGraph.Leaf r.equations)
    (p : Boundary arity a b) (hn : EquationGraph.leafName r.equations q = .inl p) :
    r.leafPartition q = .inl p := by
  unfold leafPartition
  split
  · rename_i p' hp'
    exact congrArg Sum.inl (Sum.inl.inj (hp'.symm.trans hn))
  · rename_i j hj
    cases hj.symm.trans hn

/-- Internal occurrences retain their complete original position in the partition. -/
theorem leafPartition_internal (r : Rule arity a b) (q : r.InternalLeaf) :
    r.leafPartition q.val = .inr q := by
  unfold leafPartition
  split
  · rename_i p hp
    have h := q.property
    rw [hp] at h
    cases h
  · rfl

/-- Linearity identifies all rule leaves with external ports or retained internal occurrences. -/
def leafPartitionEquiv (r : Rule arity a b) (linear : r.Linear) :
    EquationGraph.Leaf r.equations ≃ Boundary arity a b ⊕ r.InternalLeaf where
  toFun := r.leafPartition
  invFun := Sum.elim (fun p ↦ (r.boundaryOccurrence linear p).val) Subtype.val
  left_inv q := by
    cases hn : EquationGraph.leafName r.equations q with
    | inl p =>
      rw [r.leafPartition_boundary q p hn]
      exact (r.boundaryOccurrence_unique linear p q hn).symm
    | inr j =>
      have hq : (EquationGraph.leafName r.equations q).isRight := by rw [hn]; rfl
      rw [r.leafPartition_internal ⟨q, hq⟩]
      rfl
  right_inv p := by
    cases p with
    | inl p =>
      exact r.leafPartition_boundary _ p (r.boundaryOccurrence linear p).property
    | inr q => exact r.leafPartition_internal q

/-- The partition retains each external or internal wire name. -/
theorem leafPartitionEquiv_name (r : Rule arity a b) (linear : r.Linear)
    (q : EquationGraph.Leaf r.equations) :
    Sum.elim Sum.inl (fun q ↦ Sum.inr (r.internalLeafName q)) (r.leafPartitionEquiv linear q) =
      EquationGraph.leafName r.equations q := by
  cases hn : EquationGraph.leafName r.equations q with
  | inl p =>
    change Sum.elim _ _ (r.leafPartition q) = _
    rw [r.leafPartition_boundary q p hn]
    rfl
  | inr j =>
    have hq : (EquationGraph.leafName r.equations q).isRight := by rw [hn]; rfl
    change Sum.elim _ _ (r.leafPartition q) = _
    rw [r.leafPartition_internal ⟨q, hq⟩]
    exact (r.internalLeafName_eq ⟨q, hq⟩).symm.trans hn

end Geb.InteractionNet.Rule

end
