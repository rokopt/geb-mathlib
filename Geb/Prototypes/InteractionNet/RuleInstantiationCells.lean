/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleBoundaryOccurrences
public import Geb.Prototypes.InteractionNet.EquationGraphSubstitution
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Cell allocation under rule instantiation

A linear rule substitutes each auxiliary argument at exactly one boundary occurrence.
Internal names are replaced by fresh variables and contribute no cells. The instantiated
forest therefore contains exactly the rule's cells and one copy of every argument's cells.
The correspondence uses the unique boundary occurrences selected by the rule's named wires.

## Main definitions

* {lit}`Rule.argumentSubstitution` — the substitution used by textual rule instantiation.
* {lit}`Rule.argumentCellsEquiv` — replacement occurrence cells are precisely argument cells.
* {lit}`Rule.instantiateCellEquiv` — instantiated cells are the rule and argument cells.

## Main statements

* {lit}`Rule.instantiateCellEquiv_label` — rule and argument cells retain their symbols.

## Tags

interaction net, compiler, rule, instantiation, cell, allocation, linearity
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Rule

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- Rule boundary names supply actual arguments; internal names supply fresh variables. -/
def argumentSubstitution (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Boundary arity a b ⊕ Fin r.fresh → Term arity ℕ :=
  Sum.elim (Sum.elim xs ys) (fun j ↦ Term.var (r.allocated next j))

/-- Extract the argument cell represented at a boundary leaf; internal substitutions have none. -/
def argumentCell (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Σ q : EquationGraph.Leaf r.equations,
      (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q)).fragment.Cell) →
        (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Cell) := fun q ↦
  match hn : EquationGraph.leafName r.equations q.1 with
  | .inl p =>
    ⟨p, (congrArg (fun x ↦ (r.argumentSubstitution next xs ys x).fragment.Cell) hn).mp q.2⟩
  | .inr _ =>
    Fin.elim0 ((congrArg (fun x ↦ (r.argumentSubstitution next xs ys x).fragment.Cell) hn).mp q.2)

/-- Place an argument cell at the unique leaf carrying its external port name. -/
def argumentCellOccurrence (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Cell) :
    Σ q : EquationGraph.Leaf r.equations,
      (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q)).fragment.Cell :=
  ⟨(r.boundaryOccurrence linear p.1).val,
    (congrArg (fun x ↦ (r.argumentSubstitution next xs ys x).fragment.Cell)
      (r.boundaryOccurrence linear p.1).property).mpr p.2⟩

private theorem argumentCell_eq (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (q : EquationGraph.Leaf r.equations) (p : Boundary arity a b)
    (hn : EquationGraph.leafName r.equations q = .inl p)
    (c : (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q)).fragment.Cell) :
    r.argumentCell next xs ys ⟨q, c⟩ =
      ⟨p, (congrArg (fun x ↦ (r.argumentSubstitution next xs ys x).fragment.Cell) hn).mp c⟩ := by
  unfold argumentCell
  split
  · rename_i p' hp'
    have he : p' = p := Sum.inl.inj (hp'.symm.trans hn)
    subst p'
    rfl
  · rename_i j hj
    cases hj.symm.trans hn

/-- Recovering an argument cell after placing it at its selected occurrence is the identity. -/
theorem argumentCell_occurrence (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Cell) :
    r.argumentCell next xs ys (r.argumentCellOccurrence linear next xs ys p) = p := by
  rcases p with ⟨p, c⟩
  dsimp only [argumentCellOccurrence]
  rw [argumentCell_eq r next xs ys _ p (r.boundaryOccurrence linear p).property]
  exact congrArg (Sigma.mk p) (cast_cast _ _ _)

/-- Every replacement cell lies at the unique occurrence selected by its external port. -/
theorem argumentCellOccurrence_cell (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (q : Σ q : EquationGraph.Leaf r.equations,
      (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q)).fragment.Cell) :
    r.argumentCellOccurrence linear next xs ys (r.argumentCell next xs ys q) = q := by
  rcases q with ⟨q, c⟩
  match hn : EquationGraph.leafName r.equations q with
  | .inl p =>
    rw [argumentCell_eq r next xs ys q p hn]
    have hq := r.boundaryOccurrence_unique linear p q hn
    subst q
    simp [argumentCellOccurrence]
  | .inr j =>
    rw [hn] at c
    exact Fin.elim0 c

/-- Instantiation inserts each boundary argument's cells once and no cells for internal names. -/
def argumentCellsEquiv (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Σ q : EquationGraph.Leaf r.equations,
      (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q)).fragment.Cell) ≃
        (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Cell) where
  toFun := r.argumentCell next xs ys
  invFun := r.argumentCellOccurrence linear next xs ys
  left_inv := r.argumentCellOccurrence_cell linear next xs ys
  right_inv := r.argumentCell_occurrence linear next xs ys

/-- Reading a replacement cell as an argument cell preserves its agent symbol. -/
theorem argumentCell_label (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (q : Σ q : EquationGraph.Leaf r.equations,
      (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q)).fragment.Cell) :
    (Sum.elim xs ys (r.argumentCell next xs ys q).1).fragment.label
      (r.argumentCell next xs ys q).2 =
        (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q.1)).fragment.label
          q.2 := by
  rcases q with ⟨q, c⟩
  have names : (∃ p, EquationGraph.leafName r.equations q = .inl p) ∨
      (∃ j, EquationGraph.leafName r.equations q = .inr j) := by
    cases hn : EquationGraph.leafName r.equations q with
    | inl p => exact Or.inl ⟨p, rfl⟩
    | inr j => exact Or.inr ⟨j, rfl⟩
  rcases names with ⟨p, hn⟩ | ⟨j, hn⟩
  · rw [argumentCell_eq r next xs ys q p hn]
    exact Term.fragment_label_cast (congrArg (r.argumentSubstitution next xs ys) hn) c
  · rw [hn] at c
    exact Fin.elim0 c

/-- A linear instantiated rule contains its original cells and exactly one copy of each argument. -/
def instantiateCellEquiv (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Σ i, (EquationGraph.fragments (r.instantiate next xs ys) i).Cell) ≃
      (Σ i, (EquationGraph.fragments r.equations i).Cell) ⊕
        (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Cell) :=
  (EquationGraph.substCellEquiv (r.argumentSubstitution next xs ys) r.equations).trans
    (Equiv.sumCongr (Equiv.refl _) (r.argumentCellsEquiv linear next xs ys))

/-- Rule and argument cells retain their symbols in the instantiated equation forest. -/
theorem instantiateCellEquiv_label (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : Σ i, (EquationGraph.fragments (r.instantiate next xs ys) i).Cell) :
    Sum.elim
      (fun c : Σ i, (EquationGraph.fragments r.equations i).Cell ↦
        (EquationGraph.fragments r.equations c.1).label c.2)
      (fun c : Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Cell ↦
        (Sum.elim xs ys c.1).fragment.label c.2)
      (r.instantiateCellEquiv linear next xs ys p) =
        (EquationGraph.fragments (r.instantiate next xs ys) p.1).label p.2 := by
  have h := EquationGraph.substCellEquiv_label (r.argumentSubstitution next xs ys) r.equations p
  change Sum.elim _ _ ((Equiv.sumCongr (Equiv.refl _) (r.argumentCellsEquiv linear next xs ys))
    (EquationGraph.substCellEquiv (r.argumentSubstitution next xs ys) r.equations p)) = _
  cases he : EquationGraph.substCellEquiv (r.argumentSubstitution next xs ys) r.equations p with
  | inl c =>
    rw [he] at h
    exact h
  | inr c =>
    rw [he] at h
    exact (r.argumentCell_label next xs ys c).trans h

end Geb.InteractionNet.Rule

end
