/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermGraph
import Geb.Cslib.Foundations.Data.PFunctor.Free
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Graph occurrences under term substitution

Substituting terms at variable occurrences retains the original cells and inserts one
copy of each replacement's cells at each occurrence. The resulting leaves are precisely
the replacement leaves, indexed by their original occurrence. These explicit bijections
also preserve cell symbols and leaf names. They identify the cell allocations needed to
compare textual substitution with graph attachment.

## Main definitions

* {lit}`Term.substCellEquiv` — original cells and occurrence-indexed replacement cells.
* {lit}`Term.substLeafEquiv` — occurrence-indexed replacement leaves.

## Main statements

* {lit}`Term.substCellEquiv_label` — substitution's cell bijection preserves symbols.
* {lit}`Term.substLeafEquiv_name` — substitution's leaf bijection preserves names.

## Tags

interaction net, compiler, substitution, graph, cell, occurrence
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

namespace TermFragment

/-- At a variable, every inserted cell belongs to the sole replacement occurrence. -/
def variableCells (D : Type) : D ≃ Fin 0 ⊕ (Σ _ : Unit, D) where
  toFun c := .inr ⟨(), c⟩
  invFun p := match p with | .inl c => Fin.elim0 c | .inr ⟨_, c⟩ => c
  left_inv _ := rfl
  right_inv p := by
    rcases p with c | ⟨u, c⟩
    · exact Fin.elim0 c
    · rfl

/-- At a variable, every replacement leaf is indexed by the sole original occurrence. -/
def variableLeaves (D : Type) : D ≃ (Σ _ : Unit, D) where
  toFun p := ⟨(), p⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Separate original and replacement cells across an agent's family of children. -/
def substitutionCells {I : Type} (C L : I → Type) (D : ∀ i, L i → Type) :
    Unit ⊕ (Σ i, C i ⊕ (Σ p, D i p)) ≃
      (Unit ⊕ (Σ i, C i)) ⊕ (Σ p : Σ i, L i, D p.1 p.2) where
  toFun p := match p with
    | .inl u => .inl (.inl u)
    | .inr ⟨i, .inl c⟩ => .inl (.inr ⟨i, c⟩)
    | .inr ⟨i, .inr ⟨p, c⟩⟩ => .inr ⟨⟨i, p⟩, c⟩
  invFun p := match p with
    | .inl (.inl u) => .inl u
    | .inl (.inr ⟨i, c⟩) => .inr ⟨i, .inl c⟩
    | .inr ⟨⟨i, p⟩, c⟩ => .inr ⟨i, .inr ⟨p, c⟩⟩
  left_inv p := by rcases p with u | ⟨i, c | ⟨p, c⟩⟩ <;> rfl
  right_inv p := by rcases p with (u | ⟨i, c⟩) | ⟨⟨i, p⟩, c⟩ <;> rfl

end TermFragment

namespace Term

variable {α ν μ : Type} {arity : α → ℕ}

/-- Substitution retains original cells and inserts each replacement at each named occurrence. -/
def substCellEquiv (σ : ν → Term arity μ) (t : Term arity ν) :
    (t.subst σ).fragment.Cell ≃
      t.fragment.Cell ⊕ (Σ p : t.fragment.Leaf, (σ (t.fragment.name p)).fragment.Cell) :=
  PFunctor.FreeM.rec (fun x ↦ TermFragment.variableCells (σ x).fragment.Cell)
    (fun _ ts ih ↦
      (Equiv.sumCongr (Equiv.refl Unit) (sigmaCongrRight' ih)).trans
        (TermFragment.substitutionCells (fun i ↦ (fragment (ts i)).Cell)
          (fun i ↦ (fragment (ts i)).Leaf)
          (fun i p ↦ (σ ((fragment (ts i)).name p)).fragment.Cell))) t

/-- Substitution's new leaves are the replacement leaves at the original named occurrences. -/
def substLeafEquiv (σ : ν → Term arity μ) (t : Term arity ν) :
    (t.subst σ).fragment.Leaf ≃
      (Σ p : t.fragment.Leaf, (σ (t.fragment.name p)).fragment.Leaf) :=
  PFunctor.FreeM.rec (fun x ↦ TermFragment.variableLeaves (σ x).fragment.Leaf)
    (fun _ ts ih ↦ (sigmaCongrRight' ih).trans
      (Equiv.sigmaAssoc (fun i p ↦ (σ ((fragment (ts i)).name p)).fragment.Leaf)).symm) t

/-- The cell bijection preserves the symbols of both retained and inserted cells. -/
theorem substCellEquiv_label (σ : ν → Term arity μ) (t : Term arity ν)
    (c : (t.subst σ).fragment.Cell) :
    Sum.elim t.fragment.label (fun p ↦ (σ (t.fragment.name p.1)).fragment.label p.2)
      (substCellEquiv σ t c) = (t.subst σ).fragment.label c := by
  revert c
  refine PFunctor.FreeM.rec (fun _ _ ↦ rfl) (fun a ts ih c ↦ ?_) t
  rcases c with u | ⟨i, c⟩
  · rfl
  · have h := ih i c
    change Sum.elim _ _ (TermFragment.substitutionCells
      (fun i ↦ (fragment (ts i)).Cell) (fun i ↦ (fragment (ts i)).Leaf)
      (fun i p ↦ (σ ((fragment (ts i)).name p)).fragment.Cell)
      (.inr ⟨i, substCellEquiv σ (ts i) c⟩)) = _
    cases he : substCellEquiv σ (ts i) c with
    | inl d =>
      change (fragment (ts i)).label d = (subst σ (ts i)).fragment.label c
      simpa only [he, Sum.elim_inl] using h
    | inr d =>
      change (σ ((fragment (ts i)).name d.1)).fragment.label d.2 =
        (subst σ (ts i)).fragment.label c
      simpa only [he, Sum.elim_inr] using h

/-- The leaf bijection preserves the names supplied by the replacement terms. -/
theorem substLeafEquiv_name (σ : ν → Term arity μ) (t : Term arity ν)
    (p : (t.subst σ).fragment.Leaf) :
    (σ (t.fragment.name (substLeafEquiv σ t p).1)).fragment.name
      (substLeafEquiv σ t p).2 = (t.subst σ).fragment.name p := by
  revert p
  exact PFunctor.FreeM.rec (fun _ _ ↦ rfl) (fun _ _ ih p ↦ ih p.1 p.2) t

end Term

end Geb.InteractionNet

end
