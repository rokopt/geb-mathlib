/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleInstantiationAllocation
public import Geb.Prototypes.InteractionNet.ForestAttachmentContext
public import Geb.Prototypes.InteractionNet.WiringIndex
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The two families of rule-instantiation cuts

Each rule occurrence attaches either its boundary argument's root or the first end of a
fresh variable wire. Reindexing these cuts by the linear leaf partition separates the
argument attachments from the variable extensions, while preserving wires and loop counts.

## Main definitions

* {lit}`Rule.instantiationPorts` — argument and internal-variable attachments in one index family.

## Main statements

* {lit}`Rule.instantiationForest_spec` — the substituted forest is represented by these cuts.

## Tags

interaction net, rule, instantiation, substitution, attachment, splice
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Rule

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- Locate an original rule leaf among the allocated original and replacement endpoints. -/
def originalLeafEmbedding (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    EquationGraph.Leaf r.equations ↪ r.InstantiationEndpoint xs ys where
  toFun q := .inl ⟨q.1, .inl (.inr q.2)⟩
  inj' := by
    rintro ⟨i, p⟩ ⟨j, q⟩ h
    have hi := congrArg Sigma.fst (Sum.inl.inj h)
    dsimp only at hi
    subst j
    have hp := Sum.inr.inj (Sum.inl.inj (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj h)).2))
    cases hp
    rfl

/-- External ports select argument roots; internal occurrences select their variable roots. -/
def replacementRootEmbedding (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Boundary arity a b ⊕ r.InternalLeaf ↪ r.ReplacementEndpoint xs ys where
  toFun p := match p with
    | .inl p => .inl ⟨p, .inl (.inl ())⟩
    | .inr q => .inr ⟨q, false⟩
  inj' := by
    rintro (p | q) (p' | q') h
    · exact congrArg Sum.inl (congrArg Sigma.fst (Sum.inl.inj h))
    · cases h
    · cases h
    · exact congrArg Sum.inr (congrArg Sigma.fst (Sum.inr.inj h))

/-- Attach original occurrences to their argument roots or internal variable roots. -/
def instantiationPorts (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Boundary arity a b ⊕ r.InternalLeaf) × Bool ↪ r.InstantiationEndpoint xs ys where
  toFun p := if p.2 then .inr (r.replacementRootEmbedding xs ys p.1)
    else r.originalLeafEmbedding xs ys ((r.leafPartitionEquiv linear).symm p.1)
  inj' := by
    rintro ⟨p, b⟩ ⟨q, c⟩ h
    cases b <;> cases c
    · have hp := (r.leafPartitionEquiv linear).symm.injective
        ((r.originalLeafEmbedding xs ys).injective h)
      cases hp
      rfl
    · cases h
    · cases h
    · have hp := (r.replacementRootEmbedding xs ys).injective (Sum.inr.inj h)
      cases hp
      rfl

private theorem cast_root {s t : Term arity ℕ} (h : s = t) :
    (congrArg (fun t ↦ Endpoint arity t.fragment.label (Unit ⊕ t.fragment.Leaf)) h).mp
      (.inl (.inl ())) = .inl (.inl ()) := by cases h; rfl

/-- Reindexing a replacement root places it at its external argument or internal variable root. -/
theorem replacementEndpointsEquiv_root (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (q : EquationGraph.Leaf r.equations) :
    r.replacementEndpointsEquiv linear next xs ys ⟨q, .inl (.inl ())⟩ =
      r.replacementRootEmbedding xs ys (r.leafPartitionEquiv linear q) := by
  have h : r.replacementOccurrencesEquiv linear next xs ys
      (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf)) ⟨q, .inl (.inl ())⟩ =
        ⟨r.leafPartitionEquiv linear q, .inl (.inl ())⟩ :=
    congrArg (Sigma.mk (r.leafPartitionEquiv linear q))
      (cast_root (r.argumentSubstitution_partition linear next xs ys q))
  change r.partitionEndpointsEquiv next xs ys
    (r.replacementOccurrencesEquiv linear next xs ys
      (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf)) ⟨q, .inl (.inl ())⟩) = _
  rw [h]
  cases r.leafPartitionEquiv linear q <;> rfl

/-- The ordinary forest attachment cuts become the partitioned argument and variable cuts. -/
theorem instantiationAllocation_ports (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (TermFragment.forestAttachmentPorts (EquationGraph.fragments r.equations)
      (r.instantiationFragments next xs ys)).trans
        (r.instantiationAllocationEquiv linear next xs ys).toEmbedding =
          ((r.leafPartitionEquiv linear).prodCongr (Equiv.refl Bool)).toEmbedding.trans
            (r.instantiationPorts linear xs ys) := by
  ext p
  rcases p with ⟨q, b⟩
  cases b
  · change r.originalLeafEmbedding xs ys q =
      r.originalLeafEmbedding xs ys
        ((r.leafPartitionEquiv linear).symm (r.leafPartitionEquiv linear q))
    rw [Equiv.symm_apply_apply]
  · exact congrArg Sum.inr (r.replacementEndpointsEquiv_root linear next xs ys q)

/-- Constructive equality on the three finite endpoint families allocated by instantiation. -/
@[instance_reducible] def instantiationDecidableEq (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    DecidableEq (r.InstantiationEndpoint xs ys) := by
  let _ (i : EquationGraph.Root r.equations) :
      DecidableEq (Endpoint arity (EquationGraph.fragments r.equations i).label
        (Unit ⊕ (EquationGraph.fragments r.equations i).Leaf)) :=
    TermFragment.endpointDecidableEq _
  let _ (p : Boundary arity a b) : DecidableEq
      (Endpoint arity (Sum.elim xs ys p).fragment.label
        (Unit ⊕ (Sum.elim xs ys p).fragment.Leaf)) := TermFragment.endpointDecidableEq _
  let : DecidableEq r.InternalLeaf := r.internalLeafEnum.decEq
  change DecidableEq
    ((Σ i, Endpoint arity (EquationGraph.fragments r.equations i).label
      (Unit ⊕ (EquationGraph.fragments r.equations i).Leaf)) ⊕
      ((Σ p : Boundary arity a b, Endpoint arity (Sum.elim xs ys p).fragment.label
        (Unit ⊕ (Sum.elim xs ys p).fragment.Leaf)) ⊕ (Σ _ : r.InternalLeaf, Bool)))
  infer_instance

/-- Locate an attached forest's live endpoints in the separated allocation. -/
def instantiationForestEmbedding (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Endpoint arity (TermFragment.attachedForestLabel (EquationGraph.fragments r.equations)
      (r.instantiationFragments next xs ys))
      (TermFragment.AttachedForestBoundary (EquationGraph.fragments r.equations)
        (r.instantiationFragments next xs ys)) ↪ r.InstantiationEndpoint xs ys :=
  (TermFragment.forestAttachmentEmbedding (EquationGraph.fragments r.equations)
    (r.instantiationFragments next xs ys)).trans
      (r.instantiationAllocationEquiv linear next xs ys).toEmbedding

/-- The attached rule forest has exactly the matching and loop count of the partitioned cuts. -/
theorem instantiationForest_spec (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    let := r.internalLeafEnum
    let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
    let n := PortNet.sigma (fun i ↦ ((EquationGraph.fragments r.equations i).attach
      (r.instantiationFragments next xs ys i)).net)
    let g := Wiring.glue (r.instantiationPorts linear xs ys)
      (FinEnum.toList (Boundary arity a b ⊕ r.InternalLeaf)) (r.instantiationWiring xs ys, 0)
    Wiring.Respects (r.instantiationForestEmbedding linear next xs ys) n.wiring g.1 ∧
      n.loops = g.2 := by
  let := r.internalLeafEnum
  let := sigmaEnum (C := fun i ↦ (EquationGraph.fragments r.equations i).Leaf)
  let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
  let f := EquationGraph.fragments r.equations
  let g := r.instantiationFragments next xs ys
  let : DecidableEq (TermFragment.ForestAttachmentEndpoint f g) :=
    TermFragment.forestAttachmentDecidableEq f g
  let order := TermFragment.forestOrder (FinEnum.toList _) f
  have ha : Wiring.Respects (r.instantiationAllocationEquiv linear next xs ys).toEmbedding
      (TermFragment.forestAttachmentState f g).1 (r.instantiationWiring xs ys) := by
    rw [← r.instantiationAllocation_wiring linear next xs ys]
    exact Wiring.respects_map _ _
  have hg := ha.glue (TermFragment.forestAttachmentPorts f g) order
    (TermFragment.forestAttachmentState f g) (r.instantiationWiring xs ys, 0)
      (r.instantiationAllocation_loops next xs ys)
  rw [r.instantiationAllocation_ports linear next xs ys, Wiring.glue_index] at hg
  have ho := (Wiring.enum_perm_of_cover order
    (TermFragment.forestOrder_unique _ FinEnum.nodup_toList f)
    (TermFragment.forestOrder_cover _ FinEnum.mem_toList f)).map (r.leafPartitionEquiv linear)
  have hp := ho.symm.trans (Wiring.enum_perm (r.leafPartitionEquiv linear))
  rw [Wiring.glue_perm _ hp] at hg
  have h := TermFragment.forestAttach_spec f g
  exact ⟨h.1.trans hg.1, h.2.trans hg.2⟩

end Geb.InteractionNet.Rule

end
