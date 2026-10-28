/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigHeadOccurrences
public import Geb.Prototypes.InteractionNet.ConfigGraphContext
public import Geb.Prototypes.InteractionNet.PortNetSum
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The graph forest of a head equation

The two fragments of a head equation form a disjoint union with the remaining
configuration's forest. Explicit occurrence bijections identify their cells and boundary
positions with those of the complete configuration.

## Main definitions

* {lit}`Config.headForest` — the two head fragments beside the remaining forest.

## Tags

interaction net, compiler, configuration, forest, equation, disjoint union
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- Allocate the two sides of a new equation alongside the remaining configuration's forest. -/
def headForest (c : Config arity) (e : Equation arity ℕ) :
    PortNet arity (Sum.elim e.1.fragment.label (Sum.elim e.2.fragment.label c.graphLabel))
      ((Unit ⊕ e.1.fragment.Leaf) ⊕ ((Unit ⊕ e.2.fragment.Leaf) ⊕ c.GraphForestBoundary)) :=
  e.1.fragment.net.sum (e.2.fragment.net.sum c.graphForest)

/-- The head decomposition retains each cell's original symbol. -/
theorem headForest_label (c : Config arity) (e : Equation arity ℕ)
    (p : e.1.fragment.Cell ⊕ (e.2.fragment.Cell ⊕ c.GraphCell)) :
    ({ c with equations := e :: c.equations } : Config arity).graphLabel
      (c.headOccurrencesEquiv e (fun f ↦ f.Cell) p) =
        Sum.elim e.1.fragment.label (Sum.elim e.2.fragment.label c.graphLabel) p := by
  rcases p with p | (p | ⟨i | (i | i), p⟩) <;> rfl

private def headAllocationEquiv (c : Config arity) (e : Equation arity ℕ) :
    Endpoint arity e.1.fragment.label (Unit ⊕ e.1.fragment.Leaf) ⊕
      (Endpoint arity e.2.fragment.label (Unit ⊕ e.2.fragment.Leaf) ⊕
        (Σ i, Endpoint arity (c.graphFragments i).label (Unit ⊕ (c.graphFragments i).Leaf))) ≃
      Endpoint arity (Sum.elim e.1.fragment.label (Sum.elim e.2.fragment.label c.graphLabel))
        ((Unit ⊕ e.1.fragment.Leaf) ⊕ ((Unit ⊕ e.2.fragment.Leaf) ⊕ c.GraphForestBoundary)) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _)
    (PortNet.sigmaEndpointEquiv arity (fun i ↦ (c.graphFragments i).label)))).trans
      ((Equiv.sumCongr (Equiv.refl _) (PortNet.sumEndpointEquiv arity e.2.fragment.label
        c.graphLabel _ _)).trans (PortNet.sumEndpointEquiv arity e.1.fragment.label
          (Sum.elim e.2.fragment.label c.graphLabel) _ _))

private theorem headAllocation_wiring (c : Config arity) (e : Equation arity ℕ) :
    (e.1.fragment.net.wiring.sum (e.2.fragment.net.wiring.sum
      (Wiring.sigma (fun i ↦ (c.graphFragments i).net.wiring)))).map
        (c.headAllocationEquiv e) = (c.headForest e).wiring := by
  dsimp only [headAllocationEquiv, graphLabel]
  erw [Wiring.map_trans, Wiring.map_sum, Wiring.map_sum,
    Wiring.map_refl, Wiring.map_refl, Wiring.map_trans, Wiring.map_sum, Wiring.map_refl]
  rfl

private theorem headOccurrences_wiring (c : Config arity) (e : Equation arity ℕ) :
    (e.1.fragment.net.wiring.sum (e.2.fragment.net.wiring.sum
      (Wiring.sigma (fun i ↦ (c.graphFragments i).net.wiring)))).map
        (c.headOccurrencesEquiv e (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf))) =
      Wiring.sigma (fun i ↦ (({ c with equations := e :: c.equations } :
        Config arity).graphFragments i).net.wiring) := by
  have h : Wiring.Respects
      (c.headOccurrencesEquiv e (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf))).toEmbedding
      (e.1.fragment.net.wiring.sum (e.2.fragment.net.wiring.sum
        (Wiring.sigma (fun i ↦ (c.graphFragments i).net.wiring))))
      (Wiring.sigma (fun i ↦ (({ c with equations := e :: c.equations } :
        Config arity).graphFragments i).net.wiring)) := by
    rintro (p | (p | ⟨i | (i | i), p⟩)) <;> rfl
  exact h.map_eq (Wiring.respects_refl _) _ (fun _ ↦ rfl)

/-- Separating the head equation preserves the complete forest matching. -/
theorem headForest_wiring (c : Config arity) (e : Equation arity ℕ) :
    (c.headForest e).wiring.map (endpointEquiv arity
      (c.headOccurrencesEquiv e (fun f ↦ Unit ⊕ f.Leaf))
      (c.headOccurrencesEquiv e (fun f ↦ f.Cell)) (c.headForest_label e)) =
        ({ c with equations := e :: c.equations } : Config arity).graphForest.wiring := by
  let d : Config arity := { c with equations := e :: c.equations }
  have he : (c.headAllocationEquiv e).trans (endpointEquiv arity
      (c.headOccurrencesEquiv e (fun f ↦ Unit ⊕ f.Leaf))
      (c.headOccurrencesEquiv e (fun f ↦ f.Cell)) (c.headForest_label e)) =
      (c.headOccurrencesEquiv e (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf))).trans
        (PortNet.sigmaEndpointEquiv arity (fun i ↦ (d.graphFragments i).label)) := by
    ext p
    rcases p with p | (p | ⟨i, p⟩)
    · rcases p with p | ⟨v, p⟩ <;> rfl
    · rcases p with p | ⟨v, p⟩ <;> rfl
    · rcases i with i | (i | i) <;> rcases p with p | ⟨v, p⟩ <;> rfl
  erw [← headAllocation_wiring, ← Wiring.map_trans, he, Wiring.map_trans,
    headOccurrences_wiring]
  rfl

/-- Separating a textual head equation preserves the forest's closed-wire count. -/
theorem headForest_loops (c : Config arity) (e : Equation arity ℕ) :
    (c.headForest e).loops =
      ({ c with equations := e :: c.equations } : Config arity).graphForest.loops := by
  simp only [headForest, PortNet.sum, Term.fragment_loops, graphForest_loops, Nat.zero_add]

/-- The head decomposition remains an isomorphism after arbitrary boundary attachment. -/
def headForestCoupleIso {Γ : Type} [FinEnum Γ] (c : Config arity) (e : Equation arity ℕ)
    (w : Wiring (Γ ⊕ ((Unit ⊕ e.1.fragment.Leaf) ⊕
      ((Unit ⊕ e.2.fragment.Leaf) ⊕ c.GraphForestBoundary)))) :
    let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
    let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
    let d : Config arity := { c with equations := e :: c.equations }
    let := sigmaEnum (C := fun i ↦ (d.graphFragments i).Cell)
    let := sigmaEnum (C := fun i ↦ Unit ⊕ (d.graphFragments i).Leaf)
    ((c.headForest e).couple w).Iso (d.graphForest.couple
      (w.map (Equiv.sumCongr (Equiv.refl Γ)
        (c.headOccurrencesEquiv e (fun f ↦ Unit ⊕ f.Leaf))))) := by
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  let d : Config arity := { c with equations := e :: c.equations }
  let := sigmaEnum (C := fun i ↦ (d.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (d.graphFragments i).Leaf)
  exact PortNet.coupleIso _ _ _ _ _ _ (c.headForest_label e) (c.headForest_wiring e)
    (c.headForest_loops e) rfl

/-- Present the complete boundary matching with the head equation's fragments separated. -/
def headContextWiring (c : Config arity) (e : Equation arity ℕ)
    (closed : ({ c with equations := e :: c.equations } : Config arity).Closed) :
    Wiring (Fin c.interface.length ⊕ ((Unit ⊕ e.1.fragment.Leaf) ⊕
      ((Unit ⊕ e.2.fragment.Leaf) ⊕ c.GraphForestBoundary))) :=
  (({ c with equations := e :: c.equations } : Config arity).graphContextWiring closed).map
    (Equiv.sumCongr (Equiv.refl _) (c.headOccurrencesEquiv e (fun f ↦ Unit ⊕ f.Leaf))).symm

/-- The separated equation roots remain paired in the complete boundary context. -/
theorem headContextWiring_roots (c : Config arity) (e : Equation arity ℕ)
    (closed : ({ c with equations := e :: c.equations } : Config arity).Closed) :
    (c.headContextWiring e closed).partner (.inr (.inl (.inl ()))) =
      .inr (.inr (.inl (.inl ()))) := by
  let d : Config arity := { c with equations := e :: c.equations }
  let p : Fin d.interface.length ⊕ d.GraphRoot := .inr (.inr (.inl 0))
  have hr := d.graphContextRoot_respects closed p
  have h := Wiring.respects_map
    (Equiv.sumCongr (Equiv.refl (Fin c.interface.length))
      (c.headOccurrencesEquiv e (fun f ↦ Unit ⊕ f.Leaf))).symm (d.graphContextWiring closed)
  have hp := h (d.graphContextRoot p)
  rw [hr] at hp
  exact hp

/-- A complete configuration is the head equation's disjoint forest in its original context. -/
def headGraphIso (c : Config arity) (e : Equation arity ℕ)
    (closed : ({ c with equations := e :: c.equations } : Config arity).Closed) :
    let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
    let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
    (({ c with equations := e :: c.equations } : Config arity).occurrenceNet closed).Iso
      ((c.headForest e).couple (c.headContextWiring e closed)) := by
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  let d : Config arity := { c with equations := e :: c.equations }
  let := sigmaEnum (C := fun i ↦ (d.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (d.graphFragments i).Leaf)
  have h := c.headForestCoupleIso e (c.headContextWiring e closed)
  dsimp only [headContextWiring] at h
  have hw := Wiring.map_symm_map (Equiv.sumCongr (Equiv.refl (Fin c.interface.length))
    (c.headOccurrencesEquiv e (fun f ↦ Unit ⊕ f.Leaf))).symm (d.graphContextWiring closed)
  simp only [Equiv.symm_symm] at hw
  rw [hw] at h
  rw [d.occurrenceNet_eq_graphForest_couple closed]
  exact h.symm

end Geb.InteractionNet.Config

end
