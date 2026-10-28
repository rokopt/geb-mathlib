/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleInstantiationAllocation
public import Geb.Prototypes.InteractionNet.ForestAttachmentContext
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Compiling the instantiated rule forest

Each instantiated equation side is a substituted term. Its graph correspondence with
attachment lifts to the whole equation forest, preserving the original root positions,
the replacement leaf occurrences, all cell labels and the closed-wire count.

## Main definitions

* {lit}`Rule.instantiationCorrespondence` — substitution as attachment at an equation root.
* {lit}`Rule.instantiationBoundaryEquiv` — the original roots and replacement occurrences.

## Main statements

* {lit}`Rule.instantiationForest_wiring` — the compiled and attached forests correspond.

## Tags

interaction net, compiler, rule, substitution, forest, attachment
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Rule

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- Compiling a substituted equation side agrees with attachment at its original root. -/
def instantiationCorrespondence (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (i : EquationGraph.Root (r.instantiate next xs ys)) :
    TermFragment.Renaming id (EquationGraph.fragments (r.instantiate next xs ys) i)
      ((EquationGraph.fragments r.equations
        (EquationGraph.substRootEquiv (r.argumentSubstitution next xs ys) r.equations i)).attach
          (r.instantiationFragments next xs ys
            (EquationGraph.substRootEquiv (r.argumentSubstitution next xs ys) r.equations i))) :=
  (Term.fragmentEqualityCorrespondence
    (EquationGraph.term_subst (r.argumentSubstitution next xs ys) r.equations i)).trans
      (Term.substitutionCorrespondence (r.argumentSubstitution next xs ys) _)

/-- Reindex compiled instantiation cells as original forest cells and attached replacements. -/
def instantiationCellsEquiv (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  TermFragment.forestCellEquiv (EquationGraph.fragments (r.instantiate next xs ys))
    (fun i ↦ (EquationGraph.fragments r.equations i).attach (r.instantiationFragments next xs ys i))
    (EquationGraph.substRootEquiv (r.argumentSubstitution next xs ys) r.equations)
    (fun i ↦ (r.instantiationCorrespondence next xs ys i).cells)

/-- Reindex compiled instantiation boundaries by original roots and replacement leaves. -/
def instantiationBoundaryEquiv (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  TermFragment.forestBoundaryEquiv (EquationGraph.fragments (r.instantiate next xs ys))
    (fun i ↦ (EquationGraph.fragments r.equations i).attach (r.instantiationFragments next xs ys i))
    (EquationGraph.substRootEquiv (r.argumentSubstitution next xs ys) r.equations)
    (fun i ↦ (r.instantiationCorrespondence next xs ys i).leaves)

/-- The instantiation forest correspondence retains each cell's symbol. -/
theorem instantiationCellsEquiv_label (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : Σ i, (EquationGraph.fragments (r.instantiate next xs ys) i).Cell) :
    TermFragment.attachedForestLabel (EquationGraph.fragments r.equations)
      (r.instantiationFragments next xs ys) (r.instantiationCellsEquiv next xs ys p) =
        (EquationGraph.fragments (r.instantiate next xs ys) p.1).label p.2 :=
  (r.instantiationCorrespondence next xs ys p.1).labels p.2

/-- Compiling every instantiated equation side preserves the attached forest's complete matching. -/
theorem instantiationForest_wiring (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (PortNet.sigma (fun i ↦ (EquationGraph.fragments (r.instantiate next xs ys) i).net)).wiring.map
      (endpointEquiv arity (r.instantiationBoundaryEquiv next xs ys)
        (r.instantiationCellsEquiv next xs ys) (r.instantiationCellsEquiv_label next xs ys)) =
          (PortNet.sigma (fun i ↦ ((EquationGraph.fragments r.equations i).attach
            (r.instantiationFragments next xs ys i)).net)).wiring :=
  TermFragment.forest_wiring _ _ _ _ _ _
    (fun i ↦ (r.instantiationCorrespondence next xs ys i).wires)

/-- Compiling the instantiation preserves the attached forest's closed components. -/
theorem instantiationForest_loops (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (PortNet.sigma (fun i ↦ (EquationGraph.fragments (r.instantiate next xs ys) i).net)).loops =
      (PortNet.sigma (fun i ↦ ((EquationGraph.fragments r.equations i).attach
        (r.instantiationFragments next xs ys i)).net)).loops :=
  TermFragment.forest_loops _ _
    (EquationGraph.substRootEquiv (r.argumentSubstitution next xs ys) r.equations)
    (fun i ↦ (r.instantiationCorrespondence next xs ys i).loops)

end Geb.InteractionNet.Rule

end
