/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.AssemblyIso
public import Geb.Prototypes.InteractionNet.BoundaryRenaming
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Renaming the components of a term forest

A forest can be indexed in different orders without changing its assembled graph. Each
component may also rename its own cells and leaf occurrences. The matching and loop-count
proofs transport these changes through disjoint union and boundary attachment.

## Main definitions

* {lit}`TermFragment.assembleIso` — assemble corresponding forests with renamed occurrences.

## Tags

interaction net, compiler, forest, occurrence, isomorphism, assembly
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {I J : Type}

/-- Rename a dependent family's indices and its elements in each corresponding component. -/
def familyEquiv {P : I → Type} {Q : J → Type} (e : I ≃ J) (f : ∀ i, P i ≃ Q (e i)) :
    (Σ i, P i) ≃ (Σ j, Q j) :=
  (sigmaCongrRight' f).trans (Equiv.sigmaCongrLeft e)

namespace Wiring

/-- Matching-preserving component bijections preserve the disjoint matching of a whole family. -/
theorem sigma_map {P : I → Type} {Q : J → Type} (e : I ≃ J) (f : ∀ i, P i ≃ Q (e i))
    (s : ∀ i, Wiring (P i)) (t : ∀ j, Wiring (Q j))
    (h : ∀ i, (s i).map (f i) = t (e i)) :
    (sigma s).map (familyEquiv e f) = sigma t := by
  have hr : Respects (familyEquiv e f).toEmbedding (sigma s) (sigma t) := by
    rintro ⟨i, p⟩
    change Sigma.mk (e i) ((t (e i)).partner (f i p)) =
      Sigma.mk (e i) (f i ((s i).partner p))
    rw [← h i, map_partner]
  exact hr.map_eq (respects_refl _) _ (fun _ ↦ rfl)

end Wiring

namespace TermFragment

variable {α ν μ R L : Type} {arity : α → ℕ}

/-- Renaming the exposed root and leaf positions commutes with forest assembly. -/
theorem assemble_reboundary {R' L' : Type} [FinEnum I] [FinEnum R] [FinEnum L]
    [FinEnum R'] [FinEnum L'] (f : I → TermFragment arity ν)
    (roots : Wiring (R ⊕ I)) (leaves : Wiring (L ⊕ (Σ i, (f i).Leaf)))
    (r : R ≃ R') (l : L ≃ L') :
    assemble f (roots.map (Equiv.sumCongr r (Equiv.refl I)))
      (leaves.map (Equiv.sumCongr l (Equiv.refl _))) =
        (assemble f roots leaves).reboundary (Equiv.sumCongr r l) := by
  let := sigmaEnum (C := fun i ↦ (f i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (f i).Leaf)
  dsimp only [assemble]
  rw [← PortNet.couple_reboundary]
  have he : (assemblyBoundaryEquiv (R := R) (L := L) f).trans
      (Equiv.sumCongr (Equiv.sumCongr r l) (Equiv.refl _)) =
      (Equiv.sumCongr (Equiv.sumCongr r (Equiv.refl I))
        (Equiv.sumCongr l (Equiv.refl _))).trans (assemblyBoundaryEquiv f) := by
    ext p
    rcases p with (r | i) | (l | ⟨i, p⟩) <;> rfl
  have hw := ((Wiring.respects_map (Equiv.sumCongr r (Equiv.refl I)) roots).sum
    (Wiring.respects_map (Equiv.sumCongr l (Equiv.refl _)) leaves)).map_eq
      (Wiring.respects_refl _) (Equiv.sumCongr (Equiv.sumCongr r (Equiv.refl I))
        (Equiv.sumCongr l (Equiv.refl _))) (fun _ ↦ rfl)
  rw [← Wiring.map_trans, he, Wiring.map_trans, hw]

/-- Rename a forest's cells through its component index and cell bijections. -/
def forestCellEquiv (f : I → TermFragment arity ν) (g : J → TermFragment arity μ)
    (e : I ≃ J) (cells : ∀ i, (f i).Cell ≃ (g (e i)).Cell) :
    (Σ i, (f i).Cell) ≃ (Σ j, (g j).Cell) :=
  familyEquiv (P := fun i ↦ (f i).Cell) (Q := fun j ↦ (g j).Cell) e cells

/-- Rename a forest's leaves through its component index and occurrence bijections. -/
def forestLeafEquiv (f : I → TermFragment arity ν) (g : J → TermFragment arity μ)
    (e : I ≃ J) (leaves : ∀ i, (f i).Leaf ≃ (g (e i)).Leaf) :
    (Σ i, (f i).Leaf) ≃ (Σ j, (g j).Leaf) :=
  familyEquiv (P := fun i ↦ (f i).Leaf) (Q := fun j ↦ (g j).Leaf) e leaves

/-- Rename the roots and leaves of a forest's exposed boundary. -/
def forestBoundaryEquiv (f : I → TermFragment arity ν) (g : J → TermFragment arity μ)
    (e : I ≃ J) (leaves : ∀ i, (f i).Leaf ≃ (g (e i)).Leaf) :
    (Σ i, Unit ⊕ (f i).Leaf) ≃ (Σ j, Unit ⊕ (g j).Leaf) :=
  familyEquiv (P := fun i ↦ Unit ⊕ (f i).Leaf) (Q := fun j ↦ Unit ⊕ (g j).Leaf) e
    (fun i ↦ Equiv.sumCongr (Equiv.refl Unit) (leaves i))

/-- Component cell bijections preserve the symbols of the disjoint forest. -/
theorem forest_label (f : I → TermFragment arity ν) (g : J → TermFragment arity μ)
    (e : I ≃ J) (cells : ∀ i, (f i).Cell ≃ (g (e i)).Cell)
    (labels : ∀ i c, (g (e i)).label (cells i c) = (f i).label c)
    (c : Σ i, (f i).Cell) :
    (g (forestCellEquiv f g e cells c).1).label (forestCellEquiv f g e cells c).2 =
      (f c.1).label c.2 :=
  labels c.1 c.2

/-- Component graph renamings preserve the disjoint forest's matching. -/
theorem forest_wiring [FinEnum I] [FinEnum J]
    (f : I → TermFragment arity ν) (g : J → TermFragment arity μ) (e : I ≃ J)
    (cells : ∀ i, (f i).Cell ≃ (g (e i)).Cell)
    (leaves : ∀ i, (f i).Leaf ≃ (g (e i)).Leaf)
    (labels : ∀ i c, (g (e i)).label (cells i c) = (f i).label c)
    (wires : ∀ i, (f i).net.wiring.map (endpointEquiv arity
      (Equiv.sumCongr (Equiv.refl Unit) (leaves i)) (cells i) (labels i)) =
        (g (e i)).net.wiring) :
    (PortNet.sigma (fun i ↦ (f i).net)).wiring.map
      (endpointEquiv arity (forestBoundaryEquiv f g e leaves) (forestCellEquiv f g e cells)
        (forest_label f g e cells labels)) = (PortNet.sigma (fun j ↦ (g j).net)).wiring := by
  let ep := familyEquiv
    (P := fun i ↦ Endpoint arity (f i).label (Unit ⊕ (f i).Leaf))
    (Q := fun j ↦ Endpoint arity (g j).label (Unit ⊕ (g j).Leaf)) e
      (fun i ↦ endpointEquiv arity
    (Equiv.sumCongr (Equiv.refl Unit) (leaves i)) (cells i) (labels i))
  have he : (PortNet.sigmaEndpointEquiv arity (fun i ↦ (f i).label)).trans
      (endpointEquiv arity (forestBoundaryEquiv f g e leaves) (forestCellEquiv f g e cells)
        (forest_label f g e cells labels)) =
      ep.trans (PortNet.sigmaEndpointEquiv arity (fun j ↦ (g j).label)) := by
    ext p
    rcases p with ⟨i, p | ⟨c, p⟩⟩ <;> rfl
  change ((Wiring.sigma fun i ↦ (f i).net.wiring).map _).map _ = _
  rw [← Wiring.map_trans, he, Wiring.map_trans,
    Wiring.sigma_map e _ _ (fun j ↦ (g j).net.wiring) wires]
  rfl

/-- Reindexing a forest preserves the sum of its closed-wire counts. -/
theorem forest_loops [FinEnum I] [FinEnum J]
    (f : I → TermFragment arity ν) (g : J → TermFragment arity μ) (e : I ≃ J)
    (loops : ∀ i, (f i).net.loops = (g (e i)).net.loops) :
    (PortNet.sigma (fun i ↦ (f i).net)).loops =
      (PortNet.sigma (fun j ↦ (g j).net)).loops := by
  change ((FinEnum.toList I).map fun i ↦ (f i).net.loops).sum =
    ((FinEnum.toList J).map fun j ↦ (g j).net.loops).sum
  have h := ((Wiring.enum_perm e).map (fun j ↦ (g j).net.loops)).sum_eq
  simpa only [List.map_map, Function.comp_def, ← loops] using h

/-- Corresponding forests and boundary matchings assemble to isomorphic graphs. -/
def assembleIso [FinEnum I] [FinEnum J] [FinEnum R] [FinEnum L]
    (f : I → TermFragment arity ν) (g : J → TermFragment arity μ) (e : I ≃ J)
    (cells : ∀ i, (f i).Cell ≃ (g (e i)).Cell)
    (leaves : ∀ i, (f i).Leaf ≃ (g (e i)).Leaf)
    (labels : ∀ i c, (g (e i)).label (cells i c) = (f i).label c)
    (wires : ∀ i, (f i).net.wiring.map (endpointEquiv arity
      (Equiv.sumCongr (Equiv.refl Unit) (leaves i)) (cells i) (labels i)) =
        (g (e i)).net.wiring)
    (loops : ∀ i, (f i).net.loops = (g (e i)).net.loops)
    (roots : Wiring (R ⊕ I)) (roots' : Wiring (R ⊕ J))
    (leafWires : Wiring (L ⊕ (Σ i, (f i).Leaf)))
    (leafWires' : Wiring (L ⊕ (Σ j, (g j).Leaf)))
    (hr : roots.map (Equiv.sumCongr (Equiv.refl R) e) = roots')
    (hl : leafWires.map
      (Equiv.sumCongr (Equiv.refl L) (forestLeafEquiv f g e leaves)) = leafWires') :
    (assemble f roots leafWires).Iso (assemble g roots' leafWires') := by
  let := sigmaEnum (C := fun i ↦ (f i).Cell)
  let := sigmaEnum (C := fun j ↦ (g j).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (f i).Leaf)
  let := sigmaEnum (C := fun j ↦ Unit ⊕ (g j).Leaf)
  apply PortNet.coupleIso _ _ _ _ (forestBoundaryEquiv f g e leaves)
    (forestCellEquiv f g e cells) (forest_label f g e cells labels)
    (forest_wiring f g e cells leaves labels wires) (forest_loops f g e loops)
  have he : (assemblyBoundaryEquiv (R := R) (L := L) f).trans
      (Equiv.sumCongr (Equiv.refl (R ⊕ L)) (forestBoundaryEquiv f g e leaves)) =
      (Equiv.sumCongr (Equiv.sumCongr (Equiv.refl R) e)
        (Equiv.sumCongr (Equiv.refl L) (forestLeafEquiv f g e leaves))).trans
          (assemblyBoundaryEquiv g) := by
    ext p
    rcases p with (r | i) | (l | ⟨i, p⟩) <;> rfl
  rw [← Wiring.map_trans, he, Wiring.map_trans]
  have hw := Wiring.Respects.sum (Wiring.respects_map
    (Equiv.sumCongr (Equiv.refl R) e) roots)
      (Wiring.respects_map (Equiv.sumCongr (Equiv.refl L) (forestLeafEquiv f g e leaves)) leafWires)
  rw [hr, hl] at hw
  rw [hw.map_eq (Wiring.respects_refl _) _ (fun _ ↦ rfl)]

/-- Forest assembly preserves corresponding graphs with renamed external root positions. -/
def assembleIsoBoundary {R' : Type} [FinEnum I] [FinEnum J] [FinEnum R] [FinEnum R']
    [FinEnum L] (f : I → TermFragment arity ν) (g : J → TermFragment arity μ)
    (b : R ≃ R') (e : I ≃ J)
    (cells : ∀ i, (f i).Cell ≃ (g (e i)).Cell)
    (leaves : ∀ i, (f i).Leaf ≃ (g (e i)).Leaf)
    (labels : ∀ i c, (g (e i)).label (cells i c) = (f i).label c)
    (wires : ∀ i, (f i).net.wiring.map (endpointEquiv arity
      (Equiv.sumCongr (Equiv.refl Unit) (leaves i)) (cells i) (labels i)) =
        (g (e i)).net.wiring)
    (loops : ∀ i, (f i).net.loops = (g (e i)).net.loops)
    (roots : Wiring (R ⊕ I)) (roots' : Wiring (R' ⊕ J))
    (leafWires : Wiring (L ⊕ (Σ i, (f i).Leaf)))
    (leafWires' : Wiring (L ⊕ (Σ j, (g j).Leaf)))
    (hr : roots.map (Equiv.sumCongr b e) = roots')
    (hl : leafWires.map
      (Equiv.sumCongr (Equiv.refl L) (forestLeafEquiv f g e leaves)) = leafWires') :
    ((assemble f roots leafWires).reboundary (Equiv.sumCongr b (Equiv.refl L))).Iso
      (assemble g roots' leafWires') := by
  have hr' : (roots.map (Equiv.sumCongr b (Equiv.refl I))).map
      (Equiv.sumCongr (Equiv.refl R') e) = roots' := by
    rw [← Wiring.map_trans]
    have he : (Equiv.sumCongr b (Equiv.refl I)).trans (Equiv.sumCongr (Equiv.refl R') e) =
        Equiv.sumCongr b e := by ext p; cases p <;> rfl
    rw [he]
    exact hr
  have h := assembleIso f g e cells leaves labels wires loops
    (roots.map (Equiv.sumCongr b (Equiv.refl I))) roots' leafWires leafWires' hr' hl
  have he := assemble_reboundary f roots leafWires b (Equiv.refl L)
  have hi : Equiv.sumCongr (Equiv.refl L) (Equiv.refl (Σ i, (f i).Leaf)) =
      Equiv.refl _ := by ext p; cases p <;> rfl
  rw [hi, Wiring.map_refl] at he
  rw [he] at h
  exact h

end TermFragment

end Geb.InteractionNet

end
