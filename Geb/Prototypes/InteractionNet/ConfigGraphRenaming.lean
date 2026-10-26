/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigGraphIso
public import Geb.Prototypes.InteractionNet.TermGraphRenaming
public import Geb.Prototypes.InteractionNet.Substitution
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Wire-name independence of compiled configurations

Injectively renaming the wire names of a closed configuration preserves its graph.
Substitution retains the interface and equation root positions. Textual renaming also
retains each term's cell and leaf occurrences, so the resulting forest correspondence
preserves the root wires and the pairs of equally named leaves.

## Main definitions

* {lit}`Config.renameGraphIso` — compiled graphs agree after injective textual renaming.

## Tags

interaction net, compiler, configuration, substitution, alpha renaming, graph
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- The syntax term at an interface root or either side of an equation. -/
def graphTerm (c : Config arity) : c.GraphRoot → Term arity ℕ :=
  Sum.elim c.interface.get (EquationGraph.term c.equations)

/-- Configuration fragments are the translations of their selected root terms. -/
theorem graphFragments_term (c : Config arity) (i : c.GraphRoot) :
    c.graphFragments i = (c.graphTerm i).fragment := by
  cases i <;> rfl

/-- Substitution retains every external interface position. -/
def substBoundaryEquiv (σ : ℕ → Term arity ℕ) (c : Config arity) :
    Fin c.interface.length ≃ Fin (c.subst σ).interface.length :=
  finCongr (List.length_map (f := Term.subst σ) (as := c.interface)).symm

/-- Substitution retains the position of each equation. -/
def substEquationEquiv (σ : ℕ → Term arity ℕ) (c : Config arity) :
    Fin c.equations.length ≃ Fin (c.subst σ).equations.length :=
  finCongr (List.length_map
    (f := fun e : Equation arity ℕ ↦ (e.1.subst σ, e.2.subst σ)) (as := c.equations)).symm

/-- Substitution retains interface roots and both sides of every equation. -/
def substRootEquiv (σ : ℕ → Term arity ℕ) (c : Config arity) :
    c.GraphRoot ≃ (c.subst σ).GraphRoot :=
  Equiv.sumCongr (c.substBoundaryEquiv σ)
    (Equiv.sumCongr (c.substEquationEquiv σ) (c.substEquationEquiv σ))

/-- A substituted configuration translates the substituted term at each original root. -/
theorem graphFragments_subst (σ : ℕ → Term arity ℕ) (c : Config arity) (i : c.GraphRoot) :
    (c.subst σ).graphFragments (c.substRootEquiv σ i) = ((c.graphTerm i).subst σ).fragment := by
  rcases i with i | (i | i)
  · change ((c.interface.map (Term.subst σ)).get ⟨i.val, by
      simpa only [List.length_map] using i.isLt⟩).fragment =
        ((c.interface.get i).subst σ).fragment
    simp only [List.get_eq_getElem, List.getElem_map]
  · change (((c.equations.map fun e : Equation arity ℕ ↦ (e.1.subst σ, e.2.subst σ)).get ⟨i.val, by
      simpa only [List.length_map] using i.isLt⟩).1).fragment =
        (((c.equations.get i).1).subst σ).fragment
    simp only [List.get_eq_getElem, List.getElem_map]
  · change (((c.equations.map fun e : Equation arity ℕ ↦ (e.1.subst σ, e.2.subst σ)).get ⟨i.val, by
      simpa only [List.length_map] using i.isLt⟩).2).fragment =
        (((c.equations.get i).2).subst σ).fragment
    simp only [List.get_eq_getElem, List.getElem_map]

/-- Substitution does not change which root positions are joined. -/
theorem graphRootWiring_subst (σ : ℕ → Term arity ℕ) (c : Config arity) :
    c.graphRootWiring.map (Equiv.sumCongr (c.substBoundaryEquiv σ) (c.substRootEquiv σ)) =
      (c.subst σ).graphRootWiring := by
  have h : Wiring.Respects
      (Equiv.sumCongr (c.substBoundaryEquiv σ) (c.substRootEquiv σ)).toEmbedding
      c.graphRootWiring (c.subst σ).graphRootWiring := by
    rintro (i | (i | (i | i))) <;> rfl
  exact h.map_eq (Wiring.respects_refl _) _ (fun _ ↦ rfl)

/-- Textually renaming names maps the configuration's occurrence list pointwise. -/
theorem names_rename (σ : ℕ → ℕ) (c : Config arity) :
    (c.subst (fun x ↦ Term.var (σ x))).names = c.names.map σ := by
  rw [names_subst]
  simp only [Term.names_var]
  exact List.rec rfl (fun x xs ih ↦ by simp only [List.flatMap_cons, List.singleton_append,
    List.map_cons, ih]) c.names

/-- Injective wire-name changes preserve the two-ended wire condition. -/
theorem Closed.rename {c : Config arity} (h : c.Closed) (σ : ℕ → ℕ)
    (injective : Function.Injective σ) : (c.subst (fun x ↦ Term.var (σ x))).Closed := by
  intro x hx
  rw [names_rename] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  rw [List.count_map_of_injective _ _ injective]
  exact h y hy

/-- Each root fragment has the occurrence correspondence induced by its textual name change. -/
def renameFragment (σ : ℕ → ℕ) (c : Config arity) (i : c.GraphRoot) :
    TermFragment.Renaming σ (c.graphFragments i)
      ((c.subst (fun x ↦ Term.var (σ x))).graphFragments
        (c.substRootEquiv (fun x ↦ Term.var (σ x)) i)) := by
  rw [graphFragments_subst, graphFragments_term]
  exact Term.fragmentRenaming σ (c.graphTerm i)

/-- Injective renaming preserves the finite graph, including its cells and closed wires. -/
def renameGraphIso (c : Config arity) (closed : c.Closed) (σ : ℕ → ℕ)
    (injective : Function.Injective σ) :
    ((c.toFiniteNet closed).2.2.reboundary
      (c.substBoundaryEquiv (fun x ↦ Term.var (σ x)))).Iso
        ((c.subst (fun x ↦ Term.var (σ x))).toFiniteNet (closed.rename σ injective)).2.2 := by
  let d := c.subst (fun x ↦ Term.var (σ x))
  let b := c.substBoundaryEquiv (fun x ↦ Term.var (σ x))
  let e := c.substRootEquiv (fun x ↦ Term.var (σ x))
  let h := c.renameFragment σ
  apply indexedIso c d closed (closed.rename σ injective) b
  apply occurrenceIso c d closed (closed.rename σ injective) b e
    (fun i ↦ (h i).cells) (fun i ↦ (h i).leaves) (fun i ↦ (h i).labels)
    (fun i ↦ (h i).wires) (fun i ↦ (h i).loops) (graphRootWiring_subst _ c)
  intro p q hpq
  change (d.graphFragments (e p.1)).name ((h p.1).leaves p.2) =
    (d.graphFragments (e q.1)).name ((h q.1).leaves q.2)
  rw [(h p.1).names, (h q.1).names]
  exact congrArg σ hpq

end Geb.InteractionNet.Config

end
