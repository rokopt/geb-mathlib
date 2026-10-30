/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.AssemblyIso
public import Geb.Prototypes.InteractionNet.ContractionEmbedding
public import Geb.Prototypes.InteractionNet.ContractionCoupling
public import Geb.Prototypes.InteractionNet.PlugIso
public import Geb.Prototypes.InteractionNet.TermGraph
public import Aesop
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Reconstructing an active pair from its open context

An open context exposes the auxiliary ports of two removed agents. Adding their cells
and principal wire reconstructs an active pair without gluing any wires. Opening this
pair recovers the original context, including its ordered boundary and closed components.

## Main definitions

* {lit}`PortNet.reconstructPair` — add two agents at an exposed auxiliary boundary.
* {lit}`PortNet.reconstructPairOpenIso` — opening the added pair recovers the context.

## Tags

interaction net, active pair, context, reconstruction, graph, isomorphism
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

variable {α C Γ : Type} {arity : α → ℕ} {label : C → α}

/-- The two distinguished agents precede the cells of their open context. -/
def reconstructedLabel (a b : α) (label : C → α) : Unit ⊕ (Unit ⊕ C) → α :=
  Sum.elim (fun _ ↦ a) (Sum.elim (fun _ ↦ b) label)

/-- Turn the exposed auxiliary boundary into cell ports and add the principal endpoints. -/
def reconstructionEndpointEquiv (arity : α → ℕ) (a b : α) (label : C → α) :
    (Unit ⊕ Unit) ⊕ Endpoint arity label (Γ ⊕ (Fin (arity a) ⊕ Fin (arity b))) ≃
      Endpoint arity (reconstructedLabel a b label) Γ where
  toFun p := match p with
    | .inl (.inl _) => .inr ⟨.inl (), 0⟩
    | .inl (.inr _) => .inr ⟨.inr (.inl ()), 0⟩
    | .inr (.inl (.inl γ)) => .inl γ
    | .inr (.inl (.inr (.inl p))) => .inr ⟨.inl (), p.succ⟩
    | .inr (.inl (.inr (.inr p))) => .inr ⟨.inr (.inl ()), p.succ⟩
    | .inr (.inr ⟨c, p⟩) => .inr ⟨.inr (.inr c), p⟩
  invFun p := match p with
    | .inl γ => .inr (.inl (.inl γ))
    | .inr ⟨.inl _, p⟩ => Fin.cases (.inl (.inl ()))
        (fun p ↦ .inr (.inl (.inr (.inl p)))) p
    | .inr ⟨.inr (.inl _), p⟩ => Fin.cases (.inl (.inr ()))
        (fun p ↦ .inr (.inl (.inr (.inr p)))) p
    | .inr ⟨.inr (.inr c), p⟩ => .inr (.inr ⟨c, p⟩)
  left_inv p := by
    rcases p with (u | v) | ((γ | (p | p)) | ⟨c, p⟩) <;> rfl
  right_inv p := by
    rcases p with γ | ⟨u | (v | c), p⟩
    · rfl
    · exact Fin.cases rfl (fun _ ↦ rfl) p
    · exact Fin.cases rfl (fun _ ↦ rfl) p
    · rfl

/-- Add an active pair whose auxiliary ports occupy the context's exposed boundary. -/
def reconstructPair (a b : α)
    (n : PortNet arity label (Γ ⊕ (Fin (arity a) ⊕ Fin (arity b)))) :
    PortNet arity (reconstructedLabel a b label) Γ where
  wiring := (TermFragment.rootWire.sum n.wiring).map
    (reconstructionEndpointEquiv arity a b label)
  loops := n.loops

/-- The reconstructed agents share their principal wire. -/
theorem reconstructPair_active (a b : α)
    (n : PortNet arity label (Γ ⊕ (Fin (arity a) ⊕ Fin (arity b)))) :
    (n.reconstructPair a b).Active (.inl ()) (.inr (.inl ())) := rfl

/-- Removing the two reconstructed agents leaves precisely the original context cells. -/
def reconstructionCellsEquiv (C : Type) :
    RemainingCell (Sum.inl () : Unit ⊕ (Unit ⊕ C)) (.inr (.inl ())) ≃ C where
  toFun c := match c with
    | ⟨.inl _, h⟩ => (h.1 rfl).elim
    | ⟨.inr (.inl _), h⟩ => (h.2 rfl).elim
    | ⟨.inr (.inr c), _⟩ => c
  invFun c := ⟨.inr (.inr c), by constructor <;> intro h <;> cases h⟩
  left_inv c := by
    rcases c with ⟨u | (v | c), h⟩
    · exact (h.1 rfl).elim
    · exact (h.2 rfl).elim
    · rfl
  right_inv _ := rfl

/-- The retained context cells keep their original symbols. -/
theorem reconstructionCellsEquiv_label (a b : α) (label : C → α)
    (c : RemainingCell (Sum.inl () : Unit ⊕ (Unit ⊕ C)) (.inr (.inl ()))) :
    label (reconstructionCellsEquiv C c) = reconstructedLabel a b label c := by
  rcases c with ⟨u | (v | c), h⟩
  · exact (h.1 rfl).elim
  · exact (h.2 rfl).elim
  · rfl

section OpenContext

variable [DecidableEq C]

/-- Opening a reconstructed pair recovers its original context without changing any wires. -/
def reconstructPairOpenIso (a b : α)
    (n : PortNet arity label (Γ ⊕ (Fin (arity a) ⊕ Fin (arity b)))) :
    ((n.reconstructPair a b).openPair (n.reconstructPair_active a b)).Iso n := by
  let e := reconstructionEndpointEquiv (Γ := Γ) arity a b label
  have hb : Wiring.Respects Function.Embedding.inr n.wiring
      (TermFragment.rootWire.sum n.wiring) := fun _ ↦ rfl
  have hn : Wiring.Respects (Function.Embedding.inr.trans e.toEmbedding)
      n.wiring (n.reconstructPair a b).wiring :=
    hb.trans (Wiring.respects_map e _)
  refine ⟨reconstructionCellsEquiv C, reconstructionCellsEquiv_label a b label, ?_, rfl⟩
  apply ((n.reconstructPair a b).openPair_respects (n.reconstructPair_active a b)).map_eq hn
    (endpointEquiv arity (Equiv.refl _) (reconstructionCellsEquiv C)
      (reconstructionCellsEquiv_label a b label))
  intro p
  rcases p with (γ | (p | p)) | ⟨⟨u | (v | c), h⟩, p⟩
  · rfl
  · rfl
  · rfl
  · exact (h.1 rfl).elim
  · exact (h.2 rfl).elim
  · rfl

/-- Contracting a reconstructed pair inserts the replacement directly into its open context. -/
def reconstructPairContractIso {D : Type} [DecidableEq D] [DecidableEq Γ]
    (a b : α) (n : PortNet arity label (Γ ⊕ (Fin (arity a) ⊕ Fin (arity b))))
    {label' : D → α} (rhs : PortNet arity label' (Fin (arity a) ⊕ Fin (arity b))) :
    ((n.reconstructPair a b).contract (n.reconstructPair_active a b) rhs).Iso
      (n.plug rhs (FinEnum.toList _) FinEnum.nodup_toList FinEnum.mem_toList) :=
  (n.reconstructPairOpenIso a b).plug (Iso.refl rhs) _ _ _

end OpenContext

/-- Reconstructed-pair contraction can be performed before attaching the surrounding wires. -/
def reconstructPairCoupleResultIso {D Δ : Type} [FinEnum C] [FinEnum D] [FinEnum Γ] [FinEnum Δ]
    (a b : α) (n : PortNet arity label (Γ ⊕ (Fin (arity a) ⊕ Fin (arity b))))
    {label' : D → α} (rhs : PortNet arity label' (Fin (arity a) ⊕ Fin (arity b)))
    (w : Wiring (Δ ⊕ Γ)) :
    (((n.reconstructPair a b).couple w).contract
      ((n.reconstructPair a b).couple_active w (n.reconstructPair_active a b)) rhs).Iso
        ((n.plug rhs (FinEnum.toList _) FinEnum.nodup_toList FinEnum.mem_toList).couple w) := by
  let := subtypeEnum (fun v ↦ v ≠ (Sum.inl () : Unit ⊕ (Unit ⊕ C)) ∧ v ≠ .inr (.inl ()))
  have hc := contract_couple (n.reconstructPair a b) w (n.reconstructPair_active a b) rhs
  erw [← hc]
  exact (n.reconstructPairContractIso a b rhs).couple w

end Geb.InteractionNet.PortNet

end
