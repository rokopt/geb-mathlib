/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.PartialClosure
public import Geb.Prototypes.InteractionNet.AssemblyEmbedding
public import Geb.Prototypes.InteractionNet.WiringCompose
public import Geb.Prototypes.InteractionNet.WiringIndex
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Attaching the remaining context after partial closure

Closing one boundary block and assembling the other block use disjoint cuts. The two
matchings can be combined first and attached in a single operation. This keeps the cell
indices fixed and accounts for closed wires created by either family of cuts.

## Main statements

* {lit}`PortNet.close_couple` — combine internal closure and surrounding boundary assembly.

## Tags

interaction net, boundary, closure, coupling, assembly, interchange
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

variable {α C Γ B Δ : Type} {arity : α → ℕ} {label : C → α}
variable [FinEnum C] [FinEnum Γ] [FinEnum B] [FinEnum Δ]

private abbrev Ambient (arity : α → ℕ) (label : C → α) (Γ B Δ : Type) :=
  (Δ ⊕ Γ) ⊕ ClosureEndpoint arity label Γ B

private def ambientDecidableEq : DecidableEq (Ambient arity label Γ B Δ) :=
  let := sigmaEnum (C := fun c ↦ Fin (arity (label c) + 1))
  inferInstance

private local instance : DecidableEq (Ambient arity label Γ B Δ) := ambientDecidableEq

private def innerPorts : B × Bool ↪ Ambient arity label Γ B Δ :=
  (closePorts arity label Γ B).trans .inr

private def outerEmbedding : CouplingEndpoint arity label Δ Γ ↪ Ambient arity label Γ B Δ :=
  Function.Embedding.sumMap (.refl _) (closeEmbedding arity label Γ B)

private def outerPorts : Γ × Bool ↪ Ambient arity label Γ B Δ :=
  (couplePorts arity label Δ Γ).trans outerEmbedding

private def finalEmbedding : Endpoint arity label Δ ↪ Ambient arity label Γ B Δ :=
  (coupleEmbedding arity label Δ Γ).trans outerEmbedding

private def ambientEquiv : CouplingEndpoint arity label Δ (Γ ⊕ B) ≃
    Ambient arity label Γ B Δ :=
  (Equiv.sumCongr (Equiv.sumAssoc Δ Γ B).symm (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _)

private def start (n : PortNet arity label (Γ ⊕ B)) (v : Wiring B) (w : Wiring (Δ ⊕ Γ)) :
    Wiring (Ambient arity label Γ B Δ) × ℕ :=
  (w.sum (v.sum n.wiring), n.loops)

private theorem successive_spec (n : PortNet arity label (Γ ⊕ B))
    (v : Wiring B) (w : Wiring (Δ ⊕ Γ)) :
    let g := Wiring.glue outerPorts (FinEnum.toList Γ)
      (Wiring.glue innerPorts (FinEnum.toList B) (start n v w))
    Wiring.Respects finalEmbedding ((n.close v).couple w).wiring g.1 ∧
      ((n.close v).couple w).loops = g.2 := by
  dsimp only
  let s := Wiring.glue innerPorts (FinEnum.toList B) (start n v w)
  have hi := n.close_in v Function.Embedding.inr (start n v w)
    (Wiring.respects_inr w _) 0 (Nat.add_zero _)
  have he : Wiring.Respects outerEmbedding (w.sum (n.close v).wiring) s.1 := by
    rintro (p | p)
    · apply Wiring.glue_keeps
      · intro i b h; cases h
      · intro i b h; cases h
      · rfl
    · exact hi.1 p
  have h := (n.close v).couple_in w outerEmbedding s he 0 hi.2
  exact ⟨h.1, (Nat.add_zero _).symm.trans h.2⟩

omit [FinEnum C] [FinEnum Γ] [FinEnum B] [FinEnum Δ] in
private theorem combined_respects (n : PortNet arity label (Γ ⊕ B))
    (v : Wiring B) (w : Wiring (Δ ⊕ Γ)) :
    Wiring.Respects ambientEquiv.toEmbedding
      (((w.sum v).map (Equiv.sumAssoc Δ Γ B)).sum n.wiring) (start n v w).1 := by
  have h := (Wiring.respects_map_symm (Equiv.sumAssoc Δ Γ B) (w.sum v)).sum
    (Wiring.respects_refl n.wiring)
  have h' : Wiring.Respects (Equiv.sumAssoc _ _ _).toEmbedding
      ((w.sum v).sum n.wiring) (start n v w).1 := by
    rintro ((p | p) | p) <;> rfl
  exact h.trans h'

omit [FinEnum C] [FinEnum Γ] [FinEnum B] [FinEnum Δ] in
private theorem combined_ports (p : (Γ ⊕ B) × Bool) :
    ambientEquiv (couplePorts arity label Δ (Γ ⊕ B) p) =
      match p.1 with
      | .inl i => outerPorts (i, p.2)
      | .inr i => innerPorts (i, p.2) := by
  rcases p with ⟨p | p, b⟩ <;> cases b <;> rfl

/-- Closing internal positions and attaching the outer context is one complete boundary assembly. -/
theorem close_couple (n : PortNet arity label (Γ ⊕ B)) (v : Wiring B)
    (w : Wiring (Δ ⊕ Γ)) :
    (n.close v).couple w = n.couple ((w.sum v).map (Equiv.sumAssoc Δ Γ B)) := by
  have hs := successive_spec n v w
  have ht := n.couple_in ((w.sum v).map (Equiv.sumAssoc Δ Γ B))
    ambientEquiv.toEmbedding (start n v w) (combined_respects n v w) 0 (Nat.add_zero _)
  have hp : (Function.Embedding.inl.prodMap (.refl Bool)).trans
      ((couplePorts arity label Δ (Γ ⊕ B)).trans ambientEquiv.toEmbedding) = outerPorts := by
    ext p
    exact combined_ports ⟨.inl p.1, p.2⟩
  have hq : (Function.Embedding.inr.prodMap (.refl Bool)).trans
      ((couplePorts arity label Δ (Γ ⊕ B)).trans ambientEquiv.toEmbedding) = innerPorts := by
    ext p
    exact combined_ports ⟨.inr p.1, p.2⟩
  have hf : (coupleEmbedding arity label Δ (Γ ⊕ B)).trans ambientEquiv.toEmbedding =
      finalEmbedding := by
    ext p
    cases p <;> rfl
  have hd (i : Γ) (b : Bool) (j : B) (c : Bool) :
      outerPorts (arity := arity) (label := label) (Δ := Δ) (i, b) ≠ innerPorts (j, c) := by
    cases b <;> cases c <;> intro h <;> cases h
  dsimp only at hs ht
  rw [Wiring.glue_sum_enum, hp, hq, hf, Wiring.glue_glue outerPorts innerPorts hd] at ht
  apply PortNet.ext
  · have h := hs.1.map_eq ht.1 (Equiv.refl _) (fun _ ↦ rfl)
    simpa only [Wiring.map_refl] using h
  · exact hs.2.trans ((Nat.add_zero _).symm.trans ht.2).symm

end Geb.InteractionNet.PortNet

end
