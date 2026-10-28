/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleInstantiationSplices
public import Geb.Prototypes.InteractionNet.WiringRelocation
public import Geb.Prototypes.InteractionNet.WiringCompose
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Cancelling internal variable extensions during rule instantiation

An internal substitution only extends an existing leaf by a single variable wire. Closing
these attachment cuts moves the old leaf to the variable's free end without creating a
closed component. Original roots and cells, external rule leaves and argument endpoints
remain fixed. The remaining cuts are therefore precisely the argument attachments.

## Main definitions

* {lit}`Rule.argumentPorts` — cuts attaching argument fragments to external rule occurrences.
* {lit}`Rule.internalPorts` — cuts attaching variable fragments to internal rule occurrences.
* {lit}`Rule.internalRelocate` — move internal leaf connections to the surviving variable leaves.

## Main statements

* {lit}`Rule.cancel_internal_variables` — internal attachment is a relocation with no loop change.
* {lit}`Rule.instantiationForest_after_internal` — perform argument cuts after cancellation.

## Tags

interaction net, instantiation, variable, cancellation, argument, gluing
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Rule

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- The cuts attaching argument roots at external rule occurrences. -/
def argumentPorts (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Boundary arity a b × Bool ↪ r.InstantiationEndpoint xs ys :=
  (Function.Embedding.inl.prodMap (.refl Bool)).trans (r.instantiationPorts linear xs ys)

/-- The cuts extending internal occurrences by their freshly named variable wires. -/
def internalPorts (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    r.InternalLeaf × Bool ↪ r.InstantiationEndpoint xs ys :=
  (Function.Embedding.inr.prodMap (.refl Bool)).trans (r.instantiationPorts linear xs ys)

/-- Every internal variable root has a free partner outside all internal attachment cuts. -/
theorem internalPorts_free (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p q : r.InternalLeaf) (b : Bool) :
    (r.instantiationWiring xs ys).partner (r.internalPorts linear xs ys (p, true)) ≠
      r.internalPorts linear xs ys (q, b) := by
  cases b
  · intro h; cases h
  · intro h
    have hb := congrArg (fun p : Σ _ : r.InternalLeaf, Bool ↦ p.2)
      (Sum.inr.inj (Sum.inr.inj h))
    cases hb

/-- Move each old internal occurrence to the free end of its allocated variable wire. -/
def internalRelocate (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Equiv.Perm (r.InstantiationEndpoint xs ys) :=
  let := r.internalLeafEnum
  let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
  (r.instantiationWiring xs ys).relocation (r.internalPorts linear xs ys)
    (FinEnum.toList r.InternalLeaf) true

/-- Cancelling the internal variable attachments conjugates the matching without adding loops. -/
theorem cancel_internal_variables (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    let := r.internalLeafEnum
    let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
    Wiring.glue (r.internalPorts linear xs ys) (FinEnum.toList r.InternalLeaf)
      (r.instantiationWiring xs ys, 0) =
        ((r.instantiationWiring xs ys).map (r.internalRelocate linear xs ys), 0) := by
  let := r.internalLeafEnum
  let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
  exact Wiring.glue_relocation _ _ FinEnum.nodup_toList _ _ true
    (fun p _ q _ b ↦ r.internalPorts_free linear xs ys p q b)

/-- Each internal leaf moves to the free endpoint of its own variable extension. -/
theorem internalRelocate_leaf (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (q : r.InternalLeaf) :
    r.internalRelocate linear xs ys (r.originalLeafEmbedding xs ys q.val) =
      .inr (.inr ⟨q, true⟩) := by
  let := r.internalLeafEnum
  let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
  have h := Wiring.relocation_apply_cut (r.instantiationWiring xs ys)
    (r.internalPorts linear xs ys) (FinEnum.toList r.InternalLeaf) FinEnum.nodup_toList true
      (r.internalPorts_free linear xs ys) q
  simp only [FinEnum.mem_toList, ↓reduceIte] at h
  exact h

/-- Cancelling internal variables leaves every argument graph endpoint fixed. -/
theorem internalRelocate_argument (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : Σ p : Boundary arity a b, Endpoint arity (Sum.elim xs ys p).fragment.label
      (Unit ⊕ (Sum.elim xs ys p).fragment.Leaf)) :
    r.internalRelocate linear xs ys (.inr (.inl p)) = .inr (.inl p) := by
  let := r.internalLeafEnum
  let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
  apply Wiring.relocation_apply_of_outside
  intro q _
  constructor <;> intro h <;> cases h

/-- Original equation roots are untouched by the internal variable extensions. -/
theorem internalRelocate_root (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (i : EquationGraph.Root r.equations) :
    r.internalRelocate linear xs ys (.inl ⟨i, .inl (.inl ())⟩) = .inl ⟨i, .inl (.inl ())⟩ := by
  let := r.internalLeafEnum
  let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
  apply Wiring.relocation_apply_of_outside
  intro q _
  constructor
  · intro h
    have he := congrArg (fun p : r.InstantiationEndpoint xs ys ↦ match p with
      | .inl ⟨_, .inl (.inl _)⟩ => true
      | _ => false) h
    cases he
  · intro h; cases h

/-- Every original rule cell port is untouched by the internal variable extensions. -/
theorem internalRelocate_cell (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (i : EquationGraph.Root r.equations)
    (p : CellPort arity (EquationGraph.fragments r.equations i).label) :
    r.internalRelocate linear xs ys (.inl ⟨i, .inr p⟩) = .inl ⟨i, .inr p⟩ := by
  let := r.internalLeafEnum
  let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
  apply Wiring.relocation_apply_of_outside
  intro q _
  constructor
  · intro h
    have he := congrArg (fun p : r.InstantiationEndpoint xs ys ↦ match p with
      | .inl ⟨_, .inr _⟩ => true
      | _ => false) h
    cases he
  · intro h; cases h

/-- An external rule occurrence is distinct from every internal attachment and remains fixed. -/
theorem internalRelocate_external (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : Boundary arity a b) :
    r.internalRelocate linear xs ys
      (r.originalLeafEmbedding xs ys (r.boundaryOccurrence linear p).val) =
        r.originalLeafEmbedding xs ys (r.boundaryOccurrence linear p).val := by
  let := r.internalLeafEnum
  let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
  apply Wiring.relocation_apply_of_outside
  intro q _
  constructor
  · intro h
    have he := (r.originalLeafEmbedding xs ys).injective h
    have hp := (r.leafPartitionEquiv linear).apply_symm_apply (.inl p)
    have hq := (r.leafPartitionEquiv linear).apply_symm_apply (.inr q)
    have hf := hp.symm.trans ((congrArg (r.leafPartitionEquiv linear) he).trans hq)
    cases hf
  · intro h; cases h

/-- After internal cancellation, the remaining forest cuts attach only the boundary arguments. -/
theorem instantiationForest_after_internal (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    let := r.internalLeafEnum
    let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
    let n := PortNet.sigma (fun i ↦ ((EquationGraph.fragments r.equations i).attach
      (r.instantiationFragments next xs ys i)).net)
    let g := Wiring.glue (r.argumentPorts linear xs ys) (FinEnum.toList (Boundary arity a b))
      ((r.instantiationWiring xs ys).map (r.internalRelocate linear xs ys), 0)
    Wiring.Respects (r.instantiationForestEmbedding linear next xs ys) n.wiring g.1 ∧
      n.loops = g.2 := by
  let := r.internalLeafEnum
  let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
  have h := r.instantiationForest_spec linear next xs ys
  dsimp only at h ⊢
  rw [Wiring.glue_sum_enum] at h
  have hd (p : Boundary arity a b) (b : Bool) (q : r.InternalLeaf) (c : Bool) :
      r.argumentPorts linear xs ys (p, b) ≠ r.internalPorts linear xs ys (q, c) := by
    intro he
    have hp := congrArg Prod.fst ((r.instantiationPorts linear xs ys).injective he)
    cases hp
  change Wiring.Respects _ _
    (Wiring.glue (r.internalPorts linear xs ys) (FinEnum.toList r.InternalLeaf)
      (Wiring.glue (r.argumentPorts linear xs ys) (FinEnum.toList (Boundary arity a b))
        (r.instantiationWiring xs ys, 0))).1 ∧ _ at h
  erw [Wiring.glue_glue _ _ hd, r.cancel_internal_variables linear xs ys] at h
  exact h

end Geb.InteractionNet.Rule

end
