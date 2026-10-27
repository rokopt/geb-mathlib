/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphAssembly
public import Geb.Prototypes.InteractionNet.ContractionIso
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Boundary renaming through graph assembly

Boundary bijections preserve the positions exposed by a graph without changing its cells.
Applying the same boundary bijection to isomorphic graphs preserves their isomorphism.
Boundary attachment also commutes with renaming the external positions of its matching.

## Main statements

* {lit}`PortNet.couple_reboundary` — external renaming commutes with boundary attachment.

## Tags

interaction net, graph, boundary, renaming, assembly
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

variable {α C D B Γ Δ : Type} {arity : α → ℕ} {label : C → α} {label' : D → α}

/-- The identity boundary bijection leaves the graph unchanged. -/
@[simp] theorem reboundary_refl (n : PortNet arity label Γ) :
    n.reboundary (Equiv.refl Γ) = n := by
  apply PortNet.ext
  · exact (congrArg (fun e ↦ n.wiring.map e) (endpointEquiv_refl arity label)).trans
      (Wiring.map_refl _)
  · rfl

/-- Renaming the external boundary preserves exactly the same active cell pairs. -/
theorem reboundary_active_iff (n : PortNet arity label Γ) (e : Γ ≃ Δ) (a b : C) :
    (n.reboundary e).Active a b ↔ n.Active a b := by
  let p := endpointEquiv (label := label) (label' := label)
    arity e (Equiv.refl C) (fun _ ↦ rfl)
  change (n.wiring.map p).partner (p (principal arity label a)) =
    p (principal arity label b) ↔ n.wiring.partner (principal arity label a) =
      principal arity label b
  rw [Wiring.map_partner, p.injective.eq_iff]

/-- Consecutive boundary renamings compose without changing the internal graph. -/
theorem reboundary_trans {Θ : Type} (n : PortNet arity label Γ) (b : Γ ≃ Δ) (c : Δ ≃ Θ) :
    (n.reboundary b).reboundary c = n.reboundary (b.trans c) := by
  apply PortNet.ext
  · let eb := endpointEquiv (label := label) (label' := label)
      arity b (Equiv.refl C) (fun _ ↦ rfl)
    let ec := endpointEquiv (label := label) (label' := label)
      arity c (Equiv.refl C) (fun _ ↦ rfl)
    let ebc := endpointEquiv (label := label) (label' := label)
      arity (b.trans c) (Equiv.refl C) (fun _ ↦ rfl)
    have he : eb.trans ec = ebc := by
      ext p
      cases p <;> rfl
    exact (Wiring.map_trans eb ec n.wiring).symm.trans
      (congrArg (fun e ↦ n.wiring.map e) he)
  · rfl

/-- Applying the same external bijection preserves a cell isomorphism. -/
def Iso.reboundary {n : PortNet arity label Γ} {m : PortNet arity label' Γ}
    (i : n.Iso m) (b : Γ ≃ Δ) : (n.reboundary b).Iso (m.reboundary b) where
  cells := i.cells
  label_eq := i.label_eq
  wiring_eq := by
    have he : (endpointEquiv (label := label) (label' := label)
        arity b (Equiv.refl C) (fun _ ↦ rfl)).trans
        (endpointEquiv arity (Equiv.refl Δ) i.cells i.label_eq) =
        (endpointEquiv arity (Equiv.refl Γ) i.cells i.label_eq).trans
          (endpointEquiv (label := label') (label' := label')
            arity b (Equiv.refl D) (fun _ ↦ rfl)) := by
      ext p
      cases p <;> rfl
    change (n.wiring.map (endpointEquiv (label := label) (label' := label)
      arity b (Equiv.refl C) (fun _ ↦ rfl))).map
        (endpointEquiv (label := label) (label' := label')
          arity (Equiv.refl Δ) i.cells i.label_eq) =
      m.wiring.map (endpointEquiv (label := label') (label' := label')
        arity b (Equiv.refl D) (fun _ ↦ rfl))
    rw [← Wiring.map_trans, he, Wiring.map_trans, i.wiring_eq]
  loops_eq := i.loops_eq

/-- Renaming external positions before attachment agrees exactly with renaming its result. -/
theorem couple_reboundary [FinEnum C] [FinEnum B] [FinEnum Γ] [FinEnum Δ]
    (n : PortNet arity label B) (w : Wiring (Γ ⊕ B)) (b : Γ ≃ Δ) :
    n.couple (w.map (Equiv.sumCongr b (Equiv.refl B))) = (n.couple w).reboundary b := by
  let e := Equiv.sumCongr (Equiv.sumCongr b (Equiv.refl B))
    (Equiv.refl (Endpoint arity label B))
  have hs : Wiring.Respects e.toEmbedding (w.sum n.wiring)
      ((w.map (Equiv.sumCongr b (Equiv.refl B))).sum n.wiring) :=
    (Wiring.respects_map (Equiv.sumCongr b (Equiv.refl B)) w).sum
      (Wiring.respects_refl n.wiring)
  have hp : (couplePorts arity label Γ B).trans e.toEmbedding =
      couplePorts arity label Δ B := by
    ext p
    rcases p with ⟨i, bit⟩
    cases bit <;> rfl
  have hg := hs.glue (couplePorts arity label Γ B) (FinEnum.toList B)
    (w.sum n.wiring, n.loops)
    ((w.map (Equiv.sumCongr b (Equiv.refl B))).sum n.wiring, n.loops) rfl
  rw [hp] at hg
  have hl := n.couple_spec w
  have hr := n.couple_spec (w.map (Equiv.sumCongr b (Equiv.refl B)))
  apply PortNet.ext
  · symm
    apply (hl.1.trans hg.1).map_eq hr.1
      (endpointEquiv arity b (Equiv.refl C) (fun _ ↦ rfl))
    intro p
    cases p <;> rfl
  · exact hr.2.trans (hg.2.symm.trans hl.2.symm)

end Geb.InteractionNet.PortNet

end
