/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.EquationGraph
public import Geb.Prototypes.InteractionNet.ForestSubstitution
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Equation-forest cells under substitution

Substitution preserves the two root positions of each equation. Its cell allocation is
the original forest's cells together with the replacement cells indexed by each original
leaf occurrence. These structural bijections do not require linearity; linear rule
instantiation uses them to identify the inserted cells with one copy of each argument.

## Main definitions

* {lit}`EquationGraph.substRootEquiv` — retain the root positions of substituted equations.
* {lit}`EquationGraph.substCellEquiv` — retain original cells and insert replacement cells.

## Main statements

* {lit}`EquationGraph.substCellEquiv_label` — the occurrence bijection preserves cell symbols.

## Tags

interaction net, compiler, equation, forest, substitution, cell, allocation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.EquationGraph

variable {α ν μ : Type} {arity : α → ℕ}

/-- Substitution retains the positions of both sides of each equation. -/
def substRootEquiv (σ : ν → Term arity μ) (es : List (Equation arity ν)) :
    Root (es.map fun e ↦ (e.1.subst σ, e.2.subst σ)) ≃ Root es :=
  Equiv.sumCongr (finCongr (List.length_map ..)) (finCongr (List.length_map ..))

/-- At a retained equation root, the new term is the substitution of the original term. -/
theorem term_subst (σ : ν → Term arity μ) (es : List (Equation arity ν))
    (i : Root (es.map fun e ↦ (e.1.subst σ, e.2.subst σ))) :
    term (es.map fun e ↦ (e.1.subst σ, e.2.subst σ)) i =
      (term es (substRootEquiv σ es i)).subst σ := by
  rcases i with i | i <;>
    simp only [term, substRootEquiv, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Sum.elim_inl, Sum.elim_inr, List.get_eq_getElem, List.getElem_map]
  all_goals rfl

/-- A substituted equation forest retains its cells and allocates each occurrence's replacements. -/
def substCellEquiv (σ : ν → Term arity μ) (es : List (Equation arity ν)) :
    (Σ i, (fragments (es.map fun e ↦ (e.1.subst σ, e.2.subst σ)) i).Cell) ≃
      (Σ i, (fragments es i).Cell) ⊕
        (Σ q : Leaf es, (σ (leafName es q)).fragment.Cell) :=
  (familyEquiv (substRootEquiv σ es) (fun i ↦
    Term.fragmentCellEquiv (term_subst σ es i))).trans
      (Term.forestSubstCellEquiv σ (term es))

/-- The equation forest's cell allocation correspondence preserves every symbol. -/
theorem substCellEquiv_label (σ : ν → Term arity μ) (es : List (Equation arity ν))
    (p : Σ i, (fragments (es.map fun e ↦ (e.1.subst σ, e.2.subst σ)) i).Cell) :
    Sum.elim (fun c : Σ i, (fragments es i).Cell ↦ (fragments es c.1).label c.2)
      (fun c : Σ q : Leaf es, (σ (leafName es q)).fragment.Cell ↦
        (σ (leafName es c.1)).fragment.label c.2) (substCellEquiv σ es p) =
      (fragments (es.map fun e ↦ (e.1.subst σ, e.2.subst σ)) p.1).label p.2 := by
  have h := Term.forestSubstCellEquiv_label σ (term es)
    ⟨substRootEquiv σ es p.1,
      Term.fragmentCellEquiv (term_subst σ es p.1) p.2⟩
  exact h.trans (Term.fragment_label_cast (term_subst σ es p.1) p.2)

end Geb.InteractionNet.EquationGraph

end
