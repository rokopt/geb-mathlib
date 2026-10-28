/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ForestIso
public import Geb.Prototypes.InteractionNet.TermGraphRenaming
public import Geb.Prototypes.InteractionNet.TermGraphSimulation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Substitution in assembled term forests

The graph interpretation of substitution extends from one term to a forest assembled
with arbitrary root and leaf matchings. The occurrence correspondence preserves cell
symbols, leaf names, partners and closed-wire counts. Transporting the leaf matching along
that correspondence consequently gives the same assembled graph up to cell renaming.

## Main definitions

* {lit}`Term.substitutionCorrespondence` — substitution and attachment have corresponding
  cells, leaves, names and wires.
* {lit}`Term.assembleSubstIso` — the correspondence is preserved by forest assembly.
* {lit}`Term.forestSubstCellEquiv` — separate retained and inserted cells across the forest.

## Main statements

* {lit}`Term.forestSubstCellEquiv_label` — the forest allocation preserves cell symbols.

## Tags

interaction net, compiler, forest, substitution, attachment, graph, isomorphism
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

namespace Term

variable {α ν μ I R L : Type} {arity : α → ℕ}

/-- Equal terms have the same cells, transported by equality elimination. -/
def fragmentCellEquiv {s t : Term arity μ} (h : s = t) : s.fragment.Cell ≃ t.fragment.Cell where
  toFun := (congrArg (fun u ↦ u.fragment.Cell) h).mp
  invFun := (congrArg (fun u ↦ u.fragment.Cell) h).mpr
  left_inv c := by cases h; rfl
  right_inv c := by cases h; rfl

/-- Transporting a cell across an equality of terms preserves its symbol. -/
theorem fragment_label_cast {s t : Term arity μ} (h : s = t) (c : s.fragment.Cell) :
    t.fragment.label ((congrArg (fun u ↦ u.fragment.Cell) h).mp c) =
      s.fragment.label c := by
  cases h
  rfl

/-- Equal terms have the same leaf occurrences, transported by equality elimination. -/
def fragmentLeafEquiv {s t : Term arity μ} (h : s = t) : s.fragment.Leaf ≃ t.fragment.Leaf where
  toFun := (congrArg (fun u ↦ u.fragment.Leaf) h).mp
  invFun := (congrArg (fun u ↦ u.fragment.Leaf) h).mpr
  left_inv p := by cases h; rfl
  right_inv p := by cases h; rfl

/-- Transporting a leaf across an equality of terms preserves its wire name. -/
theorem fragment_name_cast {s t : Term arity μ} (h : s = t) (p : s.fragment.Leaf) :
    t.fragment.name (fragmentLeafEquiv h p) = s.fragment.name p := by
  cases h
  rfl

/-- Equal terms have a graph correspondence given by their equality transports. -/
def fragmentEqualityCorrespondence {s t : Term arity μ} (h : s = t) :
    TermFragment.Renaming id s.fragment t.fragment where
  cells := fragmentCellEquiv h
  leaves := fragmentLeafEquiv h
  labels := fragment_label_cast h
  names := fragment_name_cast h
  wires := by
    cases h
    have he : endpointEquiv arity (Equiv.sumCongr (Equiv.refl Unit) (fragmentLeafEquiv
        (rfl : s = s))) (fragmentCellEquiv (rfl : s = s))
          (fragment_label_cast (rfl : s = s)) = Equiv.refl _ := by
      ext p
      rcases p with (u | p) | ⟨c, p⟩ <;> rfl
    rw [he, Wiring.map_refl]
  loops := congrArg (fun t ↦ t.fragment.net.loops) h

/-- The unique occurrence in a variable's graph fragment. -/
def fragmentVarLeaf (x : μ) : (var (arity := arity) x).fragment.Leaf := ()

/-- A variable fragment has only its named leaf. -/
theorem fragmentVarLeaf_unique (x : μ) (p : (var (arity := arity) x).fragment.Leaf) :
    p = fragmentVarLeaf x := by
  cases p
  rfl

/-- Substitution and attachment have the same occurrence names and corresponding graph endpoints. -/
def substitutionCorrespondence (σ : ν → Term arity μ) (t : Term arity ν) :
    TermFragment.Renaming id (t.subst σ).fragment
      (t.fragment.attach (substitutionFragments σ t)) where
  cells := substCellEquiv σ t
  leaves := substLeafEquiv σ t
  labels := substCellEquiv_label σ t
  names := substLeafEquiv_name σ t
  wires := fragment_subst_wiring σ t
  loops := fragment_subst_loops σ t

/-- Separate all retained forest cells from the cells inserted at its leaf occurrences. -/
def forestSubstCellEquiv (σ : ν → Term arity μ) (ts : I → Term arity ν) :
    (Σ i, ((ts i).subst σ).fragment.Cell) ≃
      (Σ i, (ts i).fragment.Cell) ⊕
        (Σ q : Σ i, (ts i).fragment.Leaf, (σ ((ts q.1).fragment.name q.2)).fragment.Cell) :=
  (sigmaCongrRight' fun i ↦ substCellEquiv σ (ts i)).trans
    ((Equiv.sigmaSumDistrib (fun i ↦ (ts i).fragment.Cell)
      (fun i ↦ Σ p : (ts i).fragment.Leaf, (σ ((ts i).fragment.name p)).fragment.Cell)).trans
        (Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaAssoc
          (fun i (p : (ts i).fragment.Leaf) ↦ (σ ((ts i).fragment.name p)).fragment.Cell)).symm))

/-- Retained and inserted cells preserve their symbols through the forest's allocation bijection. -/
theorem forestSubstCellEquiv_label (σ : ν → Term arity μ) (ts : I → Term arity ν)
    (p : Σ i, ((ts i).subst σ).fragment.Cell) :
    Sum.elim (fun c : Σ i, (ts i).fragment.Cell ↦ (ts c.1).fragment.label c.2)
      (fun c : Σ q : Σ i, (ts i).fragment.Leaf,
        (σ ((ts q.1).fragment.name q.2)).fragment.Cell ↦
          (σ ((ts c.1.1).fragment.name c.1.2)).fragment.label c.2)
      (forestSubstCellEquiv σ ts p) = ((ts p.1).subst σ).fragment.label p.2 := by
  rcases p with ⟨i, c⟩
  have h := substCellEquiv_label σ (ts i) c
  cases he : substCellEquiv σ (ts i) c with
  | inl d =>
    dsimp [forestSubstCellEquiv, sigmaCongrRight', Equiv.sigmaSumDistrib]
    rw [he] at h ⊢
    exact h
  | inr d =>
    dsimp [forestSubstCellEquiv, sigmaCongrRight', Equiv.sigmaSumDistrib]
    rw [he] at h ⊢
    exact h

/-- Assembling substituted terms agrees with assembling their attached replacement fragments. -/
def assembleSubstIso [FinEnum I] [FinEnum R] [FinEnum L]
    (σ : ν → Term arity μ) (ts : I → Term arity ν) (roots : Wiring (R ⊕ I))
    (leaves : Wiring (L ⊕ (Σ i, ((ts i).subst σ).fragment.Leaf))) :
    let f := fun i ↦ ((ts i).subst σ).fragment
    let g := fun i ↦ (ts i).fragment.attach (substitutionFragments σ (ts i))
    (TermFragment.assemble f roots leaves).Iso
      (TermFragment.assemble g roots (leaves.map
        (Equiv.sumCongr (Equiv.refl L) (TermFragment.forestLeafEquiv f g
          (Equiv.refl I) (fun i ↦ substLeafEquiv σ (ts i)))))) := by
  intro f g
  let h := fun i ↦ substitutionCorrespondence σ (ts i)
  apply TermFragment.assembleIso f g (Equiv.refl I) (fun i ↦ (h i).cells)
    (fun i ↦ (h i).leaves) (fun i ↦ (h i).labels) (fun i ↦ (h i).wires)
    (fun i ↦ (h i).loops) roots roots
  · have he : Equiv.sumCongr (Equiv.refl R) (Equiv.refl I) = Equiv.refl _ := by
      ext p
      cases p <;> rfl
    rw [he, Wiring.map_refl]
  · rfl

end Term

end Geb.InteractionNet

end
