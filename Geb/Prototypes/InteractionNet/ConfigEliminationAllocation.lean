/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigEliminationOccurrences
public import Geb.Prototypes.InteractionNet.ConfigGraphContext
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Allocating the forest of a wire elimination

A once-occurring variable inserts one replacement fragment. All other replacements are
variable wires. The allocation below separates that fragment from the retained forest and
identifies the two boundary positions consumed by its attachment.

## Main definitions

* {lit}`Config.eliminationInsertedCellsEquiv` — the single inserted copy of the replacement.
* {lit}`Config.eliminationForestBoundaryEquiv` — roots and surviving named leaves.
* {lit}`Config.eliminationOpenBoundaryEquiv` — expose the selected leaf and replacement root.

## Tags

interaction net, compiler, substitution, elimination, forest, allocation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

namespace Term

/-- Equal terms have corresponding root, leaf and cell endpoints. -/
def fragmentEndpointEquiv {s t : Term arity ℕ} (h : s = t) :
    Endpoint arity s.fragment.label (Unit ⊕ s.fragment.Leaf) ≃
      Endpoint arity t.fragment.label (Unit ⊕ t.fragment.Leaf) :=
  endpointEquiv arity (Equiv.sumCongr (Equiv.refl Unit) (fragmentLeafEquiv h))
    (fragmentCellEquiv h) (fragment_label_cast h)

/-- Transport across term equality preserves the fragment matching. -/
theorem fragmentEndpointEquiv_wiring {s t : Term arity ℕ} (h : s = t) :
    s.fragment.net.wiring.map (fragmentEndpointEquiv h) = t.fragment.net.wiring := by
  cases h
  have he : fragmentEndpointEquiv (rfl : s = s) = Equiv.refl _ := by
    ext q
    rcases q with (u | q) | ⟨c, q⟩ <;> rfl
  rw [he, Wiring.map_refl]

end Term

namespace Config

/-- Attached forest cells, with the inserted term before the retained context cells. -/
def eliminationForestCellsEquiv (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    (Σ i, ((c.graphFragments i).attach (c.eliminationFragments x t i)).Cell) ≃
      t.fragment.Cell ⊕ c.GraphCell :=
  (Equiv.sigmaSumDistrib (fun i ↦ (c.graphFragments i).Cell)
    (fun i ↦ Σ q, (c.eliminationFragments x t i q).Cell)).trans
      ((Equiv.sumCongr (Equiv.refl _) ((Equiv.sigmaAssoc
        (fun i q ↦ (c.eliminationFragments x t i q).Cell)).symm.trans
          (c.eliminationInsertedCellsEquiv x t p hp unique))).trans (Equiv.sumComm _ _))

/-- The forest allocation retains every symbol on original and inserted cells. -/
theorem eliminationForestCellsEquiv_label (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (q : Σ i, ((c.graphFragments i).attach (c.eliminationFragments x t i)).Cell) :
    Sum.elim t.fragment.label c.graphLabel (c.eliminationForestCellsEquiv x t p hp unique q) =
      ((c.graphFragments q.1).attach (c.eliminationFragments x t q.1)).label q.2 := by
  rcases q with ⟨i, q | ⟨j, q⟩⟩
  · rfl
  · exact c.eliminationInsertedCellsEquiv_label x t p hp unique ⟨⟨i, j⟩, q⟩

/-- The roots, replacement leaves and unchanged named occurrences after elimination. -/
abbrev EliminationBoundary (c : Config arity) (x : ℕ) (t : Term arity ℕ) :=
  c.GraphRoot ⊕ (t.fragment.Leaf ⊕ {q : c.GraphLeaf // c.graphLeafName q ≠ x})

/-- Separate surviving roots from the attached forest's named leaf occurrences. -/
def eliminationForestBoundaryEquiv (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    (Σ i, Unit ⊕ ((c.graphFragments i).attach (c.eliminationFragments x t i)).Leaf) ≃
      c.EliminationBoundary x t where
  toFun q := match q with
    | ⟨i, .inl _⟩ => .inl i
    | ⟨i, .inr ⟨j, q⟩⟩ => .inr (c.eliminationReplacementLeavesEquiv x t p hp unique ⟨⟨i, j⟩, q⟩)
  invFun q := match q with
    | .inl i => ⟨i, .inl ()⟩
    | .inr q =>
      let v := (c.eliminationReplacementLeavesEquiv x t p hp unique).symm q
      ⟨v.1.1, .inr ⟨v.1.2, v.2⟩⟩
  left_inv q := by
    rcases q with ⟨i, u | ⟨j, q⟩⟩
    · rfl
    · dsimp only
      rw [Equiv.symm_apply_apply]
  right_inv q := by
    cases q with
    | inl i => rfl
    | inr q =>
      exact congrArg Sum.inr
        ((c.eliminationReplacementLeavesEquiv x t p hp unique).apply_symm_apply q)

/-- Move the selected old leaf and replacement root to the two distinguished positions. -/
def eliminationOpenBoundaryEquiv (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    (Unit ⊕ t.fragment.Leaf) ⊕ c.GraphForestBoundary ≃ Bool ⊕ c.EliminationBoundary x t where
  toFun q := match q with
    | .inl (.inl _) => .inl true
    | .inl (.inr q) => .inr (.inr (.inl q))
    | .inr ⟨i, .inl _⟩ => .inr (.inl i)
    | .inr ⟨i, .inr q⟩ => if h : c.graphLeafName ⟨i, q⟩ = x then .inl false
        else .inr (.inr (.inr ⟨⟨i, q⟩, h⟩))
  invFun q := match q with
    | .inl false => .inr ⟨p.1, .inr p.2⟩
    | .inl true => .inl (.inl ())
    | .inr (.inl i) => .inr ⟨i, .inl ()⟩
    | .inr (.inr (.inl q)) => .inl (.inr q)
    | .inr (.inr (.inr q)) => .inr ⟨q.val.1, .inr q.val.2⟩
  left_inv q := by
    rcases q with (u | q) | ⟨i, u | q⟩
    · rfl
    · rfl
    · rfl
    · dsimp only
      by_cases h : c.graphLeafName ⟨i, q⟩ = x
      · rw [dite_eq_left h]
        exact congrArg (fun q : c.GraphLeaf ↦
          (Sum.inr ⟨q.1, Sum.inr q.2⟩ : (Unit ⊕ t.fragment.Leaf) ⊕ c.GraphForestBoundary))
            (unique ⟨i, q⟩ h).symm
      · rw [dite_eq_right h]
  right_inv q := by
    rcases q with b | (i | (q | q))
    · cases b
      · exact dite_eq_left hp
      · rfl
    · rfl
    · rfl
    · exact dite_eq_right q.property

end Config

end Geb.InteractionNet

end
