/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.PartialClosure
public import Geb.Prototypes.InteractionNet.CouplingIdentity
public import Geb.Prototypes.InteractionNet.WiringIndex
public import Geb.Prototypes.InteractionNet.WiringRelocation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Removing external identity wires from partial closure

Complete boundary assembly can expose one boundary block through identity wires while
closing the other block. Those identity wires only extend existing endpoints: removing
them gives partial closure, with exactly the same cell positions, wiring and loop count.

## Main statements

* {lit}`PortNet.couple_partialIdentity` — cancel the identity wires at the exposed boundary.

## Tags

interaction net, boundary, closure, identity, cancellation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

variable {α C Γ B : Type} {arity : α → ℕ} {label : C → α}
variable [FinEnum C] [FinEnum Γ] [FinEnum B]

/-- Expose the first boundary block by identity wires and close the second by its matching. -/
def partialIdentity (w : Wiring B) : Wiring (Γ ⊕ (Γ ⊕ B)) :=
  ((Wiring.identityBoundary Γ).sum w).map (Equiv.sumAssoc Γ Γ B)

private abbrev Ambient (arity : α → ℕ) (label : C → α) (Γ B : Type) :=
  CouplingEndpoint arity label Γ (Γ ⊕ B)

private def ambientDecidableEq : DecidableEq (Ambient arity label Γ B) :=
  let := sigmaEnum (C := fun c ↦ Fin (arity (label c) + 1))
  inferInstance

private local instance : DecidableEq (Ambient arity label Γ B) := ambientDecidableEq

private def outerPorts : Γ × Bool ↪ Ambient arity label Γ B :=
  (Function.Embedding.inl.prodMap (.refl Bool)).trans (couplePorts arity label Γ (Γ ⊕ B))

private def innerPorts : B × Bool ↪ Ambient arity label Γ B :=
  (Function.Embedding.inr.prodMap (.refl Bool)).trans (couplePorts arity label Γ (Γ ⊕ B))

private def baseEmbedding : ClosureEndpoint arity label Γ B ↪ Ambient arity label Γ B :=
  Function.Embedding.sumMap (Function.Embedding.inr.trans .inr) (.refl _)

private def start (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B) :
    Wiring (Ambient arity label Γ B) × ℕ :=
  ((partialIdentity w).sum n.wiring, n.loops)

private def relocate (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B) :
    Equiv.Perm (Ambient arity label Γ B) :=
  (start n w).1.relocation outerPorts (FinEnum.toList Γ) false

omit [FinEnum C] [FinEnum Γ] [FinEnum B] in
private theorem free (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B)
    (i j : Γ) (b : Bool) :
    (start n w).1.partner (outerPorts (i, false)) ≠ outerPorts (j, b) := by
  cases b <;> intro h <;> cases h

private theorem relocate_outer (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B) (i : Γ) :
    relocate n w (.inr (.inl (.inl i))) = .inl (.inl i) := by
  have h := Wiring.relocation_apply_cut (start n w).1 outerPorts (FinEnum.toList Γ)
    FinEnum.nodup_toList false (free n w) i
  simp only [FinEnum.mem_toList, ↓reduceIte] at h
  exact h

private theorem relocate_other (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B)
    (p : Ambient arity label Γ B)
    (hp : ∀ i : Γ, p ≠ .inr (.inl (.inl i)) ∧ p ≠ .inl (.inl i)) :
    relocate n w p = p := by
  apply Wiring.relocation_apply_of_outside
  intro i _
  exact hp i

private theorem identity_spec (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B) :
    Wiring.glue outerPorts (FinEnum.toList Γ) (start n w) =
      ((start n w).1.map (relocate n w), n.loops) :=
  Wiring.glue_relocation outerPorts (FinEnum.toList Γ) FinEnum.nodup_toList
    (start n w).1 n.loops false (fun i _ j _ b ↦ free n w i j b)

private def remainingEmbedding (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B) :
    ClosureEndpoint arity label Γ B ↪ Ambient arity label Γ B :=
  baseEmbedding.trans (relocate n w).toEmbedding

private theorem remaining_respects (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B) :
    Wiring.Respects (remainingEmbedding n w) (w.sum n.wiring)
      ((start n w).1.map (relocate n w)) := by
  have h : Wiring.Respects baseEmbedding (w.sum n.wiring) (start n w).1 := by
    rintro (p | p) <;> rfl
  exact h.trans (Wiring.respects_map (relocate n w) (start n w).1)

private theorem remaining_ports (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B) :
    (closePorts arity label Γ B).trans (remainingEmbedding n w) = innerPorts := by
  ext p
  rcases p with ⟨p, b⟩
  cases b
  · exact relocate_other n w (.inl (.inr (.inr p))) (fun i ↦ by
      constructor <;> intro h <;> cases h)
  · exact relocate_other n w (.inr (.inl (.inr p))) (fun i ↦ by
      constructor <;> intro h <;> cases h)

private theorem remaining_final (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B)
    (p : Endpoint arity label Γ) :
    (closeEmbedding arity label Γ B).trans (remainingEmbedding n w) p =
      coupleEmbedding arity label Γ (Γ ⊕ B) p := by
  cases p with
  | inl i => exact relocate_outer n w i
  | inr p => exact relocate_other n w (.inr (.inr p)) (fun i ↦ by
      constructor <;> intro h <;> cases h)

/-- Identity wires at the external block can be removed before closing the remaining boundary. -/
theorem couple_partialIdentity (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B) :
    n.couple (partialIdentity w) = n.close w := by
  have hs := n.couple_spec (partialIdentity w)
  have ho : Wiring.glue (couplePorts arity label Γ (Γ ⊕ B)) (FinEnum.toList (Γ ⊕ B))
      (start n w) =
        Wiring.glue innerPorts (FinEnum.toList B)
          ((start n w).1.map (relocate n w), n.loops) := by
    erw [Wiring.glue_sum_enum]
    change Wiring.glue innerPorts (FinEnum.toList B)
      (Wiring.glue outerPorts (FinEnum.toList Γ) (start n w)) = _
    rw [identity_spec]
  change Wiring.Respects (coupleEmbedding arity label Γ (Γ ⊕ B))
    (n.couple (partialIdentity w)).wiring
      (Wiring.glue (couplePorts arity label Γ (Γ ⊕ B)) (FinEnum.toList (Γ ⊕ B))
        (start n w)).1 ∧ (n.couple (partialIdentity w)).loops =
          (Wiring.glue (couplePorts arity label Γ (Γ ⊕ B)) (FinEnum.toList (Γ ⊕ B))
            (start n w)).2 at hs
  rw [ho] at hs
  have hc := n.close_in w (remainingEmbedding n w)
    ((start n w).1.map (relocate n w), n.loops) (remaining_respects n w) 0 (Nat.add_zero _)
  rw [remaining_ports] at hc
  apply PortNet.ext
  · have he := hc.1.map_eq hs.1 (Equiv.refl _) (remaining_final n w)
    simpa only [Wiring.map_refl] using he.symm
  · exact hs.2.trans ((Nat.add_zero _).symm.trans hc.2).symm

end Geb.InteractionNet.PortNet

end
