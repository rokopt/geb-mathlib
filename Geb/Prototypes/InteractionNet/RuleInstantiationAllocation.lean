/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleInstantiationLeaves
public import Geb.Prototypes.InteractionNet.ForestAttachment
public import Geb.Prototypes.InteractionNet.TermGraphSum
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Endpoint allocation for rule instantiation

Before substitutions are attached, the allocated graph consists of the original rule
forest, one copy of each argument forest, and one variable wire for each internal leaf
occurrence. The allocation bijection separates these components and preserves their
complete matching. This makes the variable-wire cancellations independent of term casts.

## Main definitions

* {lit}`Rule.instantiationAllocationEquiv` — separate the three endpoint families.

## Main statements

* {lit}`Rule.instantiationAllocation_wiring` — allocation preserves every original matching.

## Tags

interaction net, compiler, rule, instantiation, allocation, endpoint
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Rule

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- The graph fragment substituted at each original rule-leaf occurrence. -/
def instantiationFragments (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (i : EquationGraph.Root r.equations) (q : (EquationGraph.fragments r.equations i).Leaf) :
    TermFragment arity ℕ :=
  (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations ⟨i, q⟩)).fragment

/-- All replacement endpoints, separated into argument graphs and internal variable wires. -/
abbrev ReplacementEndpoint (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  (Σ p : Boundary arity a b, Endpoint arity (Sum.elim xs ys p).fragment.label
    (Unit ⊕ (Sum.elim xs ys p).fragment.Leaf)) ⊕ (Σ _ : r.InternalLeaf, Bool)

/-- Identify the two endpoints of each internal variable while retaining argument endpoints. -/
def partitionEndpointsEquiv (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Σ q, Endpoint arity (r.partitionTerm next xs ys q).fragment.label
      (Unit ⊕ (r.partitionTerm next xs ys q).fragment.Leaf)) ≃ r.ReplacementEndpoint xs ys where
  toFun p := match p with
    | ⟨.inl p, q⟩ => .inl ⟨p, q⟩
    | ⟨.inr p, q⟩ => .inr ⟨p, TermFragment.varEndpointEquiv _ q⟩
  invFun p := match p with
    | .inl ⟨p, q⟩ => ⟨.inl p, q⟩
    | .inr ⟨p, b⟩ => ⟨.inr p, (TermFragment.varEndpointEquiv _).symm b⟩
  left_inv p := by
    rcases p with ⟨p | p, q⟩
    · rfl
    · rcases q with (u | u) | ⟨c, q⟩
      · rfl
      · rfl
      · exact Fin.elim0 c
  right_inv p := by
    rcases p with ⟨p, q⟩ | ⟨p, b⟩
    · rfl
    · exact congrArg (fun b ↦ Sum.inr (Sigma.mk p b))
        ((TermFragment.varEndpointEquiv _).apply_symm_apply b)

/-- Reindex every allocated replacement endpoint by its argument or internal occurrence. -/
def replacementEndpointsEquiv (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Σ q : EquationGraph.Leaf r.equations,
      Endpoint arity (r.instantiationFragments next xs ys q.1 q.2).label
        (Unit ⊕ (r.instantiationFragments next xs ys q.1 q.2).Leaf)) ≃
          r.ReplacementEndpoint xs ys :=
  (r.replacementOccurrencesEquiv linear next xs ys
    (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf))).trans
      (r.partitionEndpointsEquiv next xs ys)

/-- Discard the empty cell type of each internal variable, retaining only argument cells. -/
def partitionCellsEquiv (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Σ q, (r.partitionTerm next xs ys q).fragment.Cell) ≃
      (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Cell) where
  toFun p := match p with
    | ⟨.inl p, c⟩ => ⟨p, c⟩
    | ⟨.inr _, c⟩ => Fin.elim0 c
  invFun p := ⟨.inl p.1, p.2⟩
  left_inv p := by
    rcases p with ⟨p | p, c⟩
    · rfl
    · exact Fin.elim0 c
  right_inv p := by rcases p with ⟨p, c⟩; rfl

/-- The endpoint allocation's cell component retains exactly one copy of each argument cell. -/
def replacementCellsEquiv (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Σ q : EquationGraph.Leaf r.equations,
      (r.instantiationFragments next xs ys q.1 q.2).Cell) ≃
        (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Cell) :=
  (r.replacementOccurrencesEquiv linear next xs ys (fun f ↦ f.Cell)).trans
    (r.partitionCellsEquiv next xs ys)

/-- The allocated argument cell retains its symbol. -/
theorem replacementCellsEquiv_label (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : Σ q : EquationGraph.Leaf r.equations,
      (r.instantiationFragments next xs ys q.1 q.2).Cell) :
    let q := r.replacementCellsEquiv linear next xs ys p
    (Sum.elim xs ys q.1).fragment.label q.2 =
      (r.instantiationFragments next xs ys p.1.1 p.1.2).label p.2 := by
  have h (q : Σ p, (r.partitionTerm next xs ys p).fragment.Cell) :
      (Sum.elim xs ys (r.partitionCellsEquiv next xs ys q).1).fragment.label
        (r.partitionCellsEquiv next xs ys q).2 =
          (r.partitionTerm next xs ys q.1).fragment.label q.2 := by
    rcases q with ⟨q | q, c⟩
    · rfl
    · exact Fin.elim0 c
  exact (h (r.replacementOccurrencesEquiv linear next xs ys (fun f ↦ f.Cell) p)).trans
    (Term.fragment_label_cast (r.argumentSubstitution_partition linear next xs ys p.1) p.2)

private theorem partition_cast_leaf (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : Boundary arity a b ⊕ r.InternalLeaf) (t : Term arity ℕ)
    (h : t = r.partitionTerm next xs ys p) (q : t.fragment.Leaf) :
    r.partitionEndpointsEquiv next xs ys ⟨p,
      (congrArg (fun t ↦ Endpoint arity t.fragment.label (Unit ⊕ t.fragment.Leaf)) h).mp
        (.inl (.inr q))⟩ =
      match r.partitionLeavesEquiv next xs ys
        ⟨p, (congrArg (fun t ↦ t.fragment.Leaf) h).mp q⟩ with
      | .inl ⟨p, q⟩ => .inl ⟨p, .inl (.inr q)⟩
      | .inr p => .inr ⟨p, true⟩ := by
  subst t
  cases p <;> rfl

/-- The endpoint and leaf allocations agree on every replacement's surviving named end. -/
theorem replacementEndpointsEquiv_leaf (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : EquationGraph.Leaf r.equations)
    (q : (r.instantiationFragments next xs ys p.1 p.2).Leaf) :
    r.replacementEndpointsEquiv linear next xs ys ⟨p, .inl (.inr q)⟩ =
      match r.replacementLeavesEquiv linear next xs ys ⟨p, q⟩ with
      | .inl ⟨p, q⟩ => .inl ⟨p, .inl (.inr q)⟩
      | .inr p => .inr ⟨p, true⟩ :=
  partition_cast_leaf r next xs ys _ _
    (r.argumentSubstitution_partition linear next xs ys p) q

private theorem partition_cast_cell (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : Boundary arity a b ⊕ r.InternalLeaf) (t : Term arity ℕ)
    (h : t = r.partitionTerm next xs ys p) (c : t.fragment.Cell)
    (v : Fin (arity (t.fragment.label c) + 1))
    (hl : (Sum.elim xs ys (r.partitionCellsEquiv next xs ys
      ⟨p, (congrArg (fun t ↦ t.fragment.Cell) h).mp c⟩).1).fragment.label
        (r.partitionCellsEquiv next xs ys
          ⟨p, (congrArg (fun t ↦ t.fragment.Cell) h).mp c⟩).2 = t.fragment.label c) :
    r.partitionEndpointsEquiv next xs ys ⟨p,
      (congrArg (fun t : Term arity ℕ ↦
        Endpoint arity t.fragment.label (Unit ⊕ t.fragment.Leaf)) h).mp
        (.inr ⟨c, v⟩)⟩ =
      let q := r.partitionCellsEquiv next xs ys
        ⟨p, (congrArg (fun t ↦ t.fragment.Cell) h).mp c⟩
      .inl ⟨q.1, .inr ⟨q.2, Fin.cast (congrArg (fun a ↦ arity a + 1) hl.symm) v⟩⟩ := by
  subst t
  cases p with
  | inl p => rfl
  | inr p => exact Fin.elim0 c

/-- The endpoint and cell allocations preserve the same cell and numeric port position. -/
theorem replacementEndpointsEquiv_cell (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : EquationGraph.Leaf r.equations)
    (c : (r.instantiationFragments next xs ys p.1 p.2).Cell)
    (v : Fin (arity ((r.instantiationFragments next xs ys p.1 p.2).label c) + 1)) :
    r.replacementEndpointsEquiv linear next xs ys ⟨p, .inr ⟨c, v⟩⟩ =
      let q := r.replacementCellsEquiv linear next xs ys ⟨p, c⟩
      .inl ⟨q.1, .inr ⟨q.2, Fin.cast (congrArg (fun a ↦ arity a + 1)
        (r.replacementCellsEquiv_label linear next xs ys ⟨p, c⟩).symm) v⟩⟩ :=
  partition_cast_cell r next xs ys _ _
    (r.argumentSubstitution_partition linear next xs ys p) c v
      (r.replacementCellsEquiv_label linear next xs ys ⟨p, c⟩)

/-- The disjoint argument matchings and the two ends of each allocated internal variable. -/
def replacementWiring (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Wiring (r.ReplacementEndpoint xs ys) :=
  (Wiring.sigma (fun p ↦ (Sum.elim xs ys p).fragment.net.wiring)).sum
    (Wiring.sigma (fun _ : r.InternalLeaf ↦ Wiring.wire))

private theorem cast_partner {s t : Term arity ℕ} (h : s = t)
    (p : Endpoint arity s.fragment.label (Unit ⊕ s.fragment.Leaf)) :
    t.fragment.net.wiring.partner
      ((congrArg (fun t ↦ Endpoint arity t.fragment.label (Unit ⊕ t.fragment.Leaf)) h).mp p) =
        (congrArg (fun t ↦ Endpoint arity t.fragment.label (Unit ⊕ t.fragment.Leaf)) h).mp
          (s.fragment.net.wiring.partner p) := by cases h; rfl

private theorem replacementOccurrences_respects (r : Rule arity a b) (linear : r.Linear)
    (next : ℕ) (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Wiring.Respects (r.replacementOccurrencesEquiv linear next xs ys
      (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf))).toEmbedding
        (Wiring.sigma (fun q : EquationGraph.Leaf r.equations ↦
          (r.instantiationFragments next xs ys q.1 q.2).net.wiring))
        (Wiring.sigma (fun q ↦ (r.partitionTerm next xs ys q).fragment.net.wiring)) := by
  rintro ⟨q, p⟩
  exact congrArg (Sigma.mk (r.leafPartitionEquiv linear q))
    (cast_partner (r.argumentSubstitution_partition linear next xs ys q) p)

/-- Reindexing the replacements preserves the argument matchings and each internal variable wire. -/
theorem replacementEndpoints_respects (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Wiring.Respects (r.replacementEndpointsEquiv linear next xs ys).toEmbedding
      (Wiring.sigma (fun q : EquationGraph.Leaf r.equations ↦
        (r.instantiationFragments next xs ys q.1 q.2).net.wiring)) (r.replacementWiring xs ys) := by
  have h : Wiring.Respects (r.partitionEndpointsEquiv next xs ys).toEmbedding
      (Wiring.sigma (fun q ↦ (r.partitionTerm next xs ys q).fragment.net.wiring))
        (r.replacementWiring xs ys) := by
    rintro ⟨p | q, e⟩
    · rfl
    · rcases e with (u | u) | ⟨c, p⟩
      · rfl
      · rfl
      · exact Fin.elim0 c
  exact (replacementOccurrences_respects r linear next xs ys).trans h

/-- Original rule endpoints, argument endpoints and the allocated internal variable ends. -/
abbrev InstantiationEndpoint (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  (Σ i, Endpoint arity (EquationGraph.fragments r.equations i).label
    (Unit ⊕ (EquationGraph.fragments r.equations i).Leaf)) ⊕ r.ReplacementEndpoint xs ys

/-- Separate the original forest from its partitioned replacement graphs. -/
def instantiationAllocationEquiv (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    TermFragment.ForestAttachmentEndpoint (EquationGraph.fragments r.equations)
      (r.instantiationFragments next xs ys) ≃ r.InstantiationEndpoint xs ys :=
  (Equiv.sigmaSumDistrib
    (fun i ↦ Endpoint arity (EquationGraph.fragments r.equations i).label
      (Unit ⊕ (EquationGraph.fragments r.equations i).Leaf))
    (fun i ↦ Σ q, Endpoint arity (r.instantiationFragments next xs ys i q).label
      (Unit ⊕ (r.instantiationFragments next xs ys i q).Leaf))).trans
        (Equiv.sumCongr (Equiv.refl _) ((Equiv.sigmaAssoc
          (fun i q ↦ Endpoint arity (r.instantiationFragments next xs ys i q).label
            (Unit ⊕ (r.instantiationFragments next xs ys i q).Leaf))).symm.trans
              (r.replacementEndpointsEquiv linear next xs ys)))

/-- Allocate the original rule forest alongside the arguments and the separate variable wires. -/
def instantiationWiring (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Wiring (r.InstantiationEndpoint xs ys) :=
  (Wiring.sigma (fun i ↦ (EquationGraph.fragments r.equations i).net.wiring)).sum
    (r.replacementWiring xs ys)

/-- The complete allocation bijection preserves the disjoint original and replacement matchings. -/
theorem instantiationAllocation_wiring (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (TermFragment.forestAttachmentState (EquationGraph.fragments r.equations)
      (r.instantiationFragments next xs ys)).1.map
        (r.instantiationAllocationEquiv linear next xs ys) = r.instantiationWiring xs ys := by
  have h : Wiring.Respects (r.instantiationAllocationEquiv linear next xs ys).toEmbedding
      (TermFragment.forestAttachmentState (EquationGraph.fragments r.equations)
        (r.instantiationFragments next xs ys)).1 (r.instantiationWiring xs ys) := by
    rintro ⟨i, p | ⟨q, p⟩⟩
    · rfl
    · exact congrArg Sum.inr (r.replacementEndpoints_respects linear next xs ys ⟨⟨i, q⟩, p⟩)
  exact h.map_eq (Wiring.respects_refl _) _ (fun _ ↦ rfl)

/-- The unassembled allocation has no closed wires before either family of cuts is performed. -/
theorem instantiationAllocation_loops (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (TermFragment.forestAttachmentState (EquationGraph.fragments r.equations)
      (r.instantiationFragments next xs ys)).2 = 0 := by
  simp [TermFragment.forestAttachmentState, TermFragment.attachmentState,
    instantiationFragments, EquationGraph.fragments, Term.fragment_loops]

end Geb.InteractionNet.Rule

end
