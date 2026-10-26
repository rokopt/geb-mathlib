/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphAssembly
public import Geb.Prototypes.InteractionNet.WiringIndex
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Wires preserved by boundary attachment

Boundary attachment leaves wires between internal cell ports unchanged. When a cell port
meets a boundary position that the external matching connects to an external endpoint, the
splice connects that cell port directly to the external endpoint. The proof moves this cut
to the front of the gluing order, then observes that later cuts leave the resulting wire alone.
Joining two boundary holes similarly joins the cell ports incident to those holes.

## Main statements

* {lit}`PortNet.couple_internal_wire` — internal cell wires are unchanged.
* {lit}`PortNet.couple_external_wire` — a boundary wire extends to its external endpoint.
* {lit}`PortNet.couple_boundary_wire` — joining boundary holes joins their incident cell ports.

## Tags

interaction net, graph, boundary, attachment, wire, assembly
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

variable {α C B Γ : Type} {arity : α → ℕ} {label : C → α}
variable [FinEnum C] [FinEnum B] [FinEnum Γ]

/-- A wire between cell ports is unaffected by attaching the external boundary matching. -/
theorem couple_internal_wire (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    (p q : CellPort arity label) (h : n.wiring.partner (.inr p) = .inr q) :
    (n.couple w).wiring.partner (.inr p) = .inr q := by
  have hs := n.couple_spec w
  apply (coupleEmbedding arity label Γ B).injective
  apply (hs.1 (.inr p)).symm.trans
  apply Wiring.glue_keeps
  · intro i bit; cases bit <;> intro h <;> cases h
  · intro i bit; cases bit <;> intro h <;> cases h
  · exact congrArg Sum.inr h

/-- Attaching a matched external endpoint extends the cell's boundary wire to that endpoint. -/
theorem couple_external_wire (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    (p : CellPort arity label) (b : B) (γ : Γ)
    (hn : n.wiring.partner (.inr p) = .inl b) (hw : w.partner (.inr b) = .inl γ) :
    (n.couple w).wiring.partner (.inr p) = .inl γ := by
  have hs := n.couple_spec w
  apply (coupleEmbedding arity label Γ B).injective
  apply (hs.1 (.inr p)).symm.trans
  have order := Wiring.perm_cons_erase b (FinEnum.toList B) (FinEnum.mem_toList b)
  rw [Wiring.glue_perm (couplePorts arity label Γ B) order]
  change (Wiring.glue (couplePorts arity label Γ B) ((FinEnum.toList B).erase b)
    (Wiring.glueAt (couplePorts arity label Γ B) (w.sum n.wiring, n.loops) b)).1.partner
      (.inr (.inr p)) = .inl (.inl γ)
  apply Wiring.glue_keeps
  · intro i bit; cases bit <;> intro h <;> cases h
  · intro i bit; cases bit <;> intro h <;> cases h
  · have hr : n.wiring.partner (.inl b) = .inr p := by
      have h := congrArg n.wiring.partner hn
      simpa only [Wiring.partner_partner] using h.symm
    have h := Wiring.force_partner_right (w.sum n.wiring)
      (Wiring.pair_ne (couplePorts arity label Γ B) b)
    change ((w.sum n.wiring).force (.inl (.inr b)) (.inr (.inl b))).partner
      (.inr (n.wiring.partner (.inl b))) = .inl (w.partner (.inr b)) at h
    rw [hr, hw] at h
    exact h

/-- Joining two boundary positions joins the cell ports incident to those positions. -/
theorem couple_boundary_wire (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    (p q : CellPort arity label) (b c : B)
    (hp : n.wiring.partner (.inr p) = .inl b) (hq : n.wiring.partner (.inr q) = .inl c)
    (hw : w.partner (.inr b) = .inr c) :
    (n.couple w).wiring.partner (.inr p) = .inr q := by
  let : DecidableEq C := FinEnum.decEq
  let : DecidableEq B := FinEnum.decEq
  let : DecidableEq Γ := FinEnum.decEq
  let : DecidableEq (Endpoint arity label B) :=
    inferInstanceAs (DecidableEq (B ⊕ (Σ c : C, Fin (arity (label c) + 1))))
  let : DecidableEq (CouplingEndpoint arity label Γ B) :=
    @instDecidableEqSum (Γ ⊕ B) (Endpoint arity label B) inferInstance inferInstance
  have hbc : b ≠ c := by
    intro h
    exact w.fixedPointFree (.inr b) (hw.trans (congrArg Sum.inr h.symm))
  have hbp : n.wiring.partner (.inl b) = .inr p := by
    exact (n.wiring.partner_eq_iff.mp hp).symm
  have hcq : n.wiring.partner (.inl c) = .inr q := by
    exact (n.wiring.partner_eq_iff.mp hq).symm
  let ports := couplePorts arity label Γ B
  let s : Wiring (CouplingEndpoint arity label Γ B) × ℕ := (w.sum n.wiring, n.loops)
  let s₁ := Wiring.glueAt ports s b
  let s₂ := Wiring.glueAt ports s₁ c
  have hb : s₁.1.partner (ports (c, false)) = .inr (.inr p) := by
    have h := Wiring.force_partner_left (w.sum n.wiring) (Wiring.pair_ne ports b)
    change ((w.sum n.wiring).force (.inl (.inr b)) (.inr (.inl b))).partner
      (.inl (w.partner (.inr b))) = .inr (n.wiring.partner (.inl b)) at h
    rw [hw, hbp] at h
    exact h
  have hc : s₁.1.partner (ports (c, true)) = .inr (.inr q) := by
    apply Wiring.force_keeps (w.sum n.wiring) (Wiring.pair_ne ports b)
    · intro h; cases h
    · intro h
      exact hbc (Sum.inl.inj (Sum.inr.inj h)).symm
    · intro h; cases h
    · intro h; cases h
    · exact congrArg Sum.inr hcq
  have hfinal : s₂.1.partner (.inr (.inr p)) = .inr (.inr q) := by
    have h := Wiring.force_partner_left s₁.1 (Wiring.pair_ne ports c)
    rw [hb, hc] at h
    exact h
  have first := Wiring.perm_cons_erase b (FinEnum.toList B) (FinEnum.mem_toList b)
  have mem : c ∈ (FinEnum.toList B).erase b :=
    (List.mem_cons.mp (first.mem_iff.mp (FinEnum.mem_toList c))).resolve_left hbc.symm
  have order := first.trans
    (List.Perm.cons b (Wiring.perm_cons_erase c ((FinEnum.toList B).erase b)
      mem))
  have hs := n.couple_spec w
  apply (coupleEmbedding arity label Γ B).injective
  apply (hs.1 (.inr p)).symm.trans
  rw [Wiring.glue_perm ports order]
  change (Wiring.glue ports (((FinEnum.toList B).erase b).erase c) s₂).1.partner
    (.inr (.inr p)) = .inr (.inr q)
  exact Wiring.glue_keeps ports _ s₂
    (by intro i bit; cases bit <;> intro h <;> cases h)
    (by intro i bit; cases bit <;> intro h <;> cases h) hfinal

end Geb.InteractionNet.PortNet

end
