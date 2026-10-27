/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigGraphRenaming
public import Geb.Prototypes.InteractionNet.ForestSubstitution
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Configuration substitution by graph attachment

Compiling a substituted configuration agrees with attaching the replacement term graphs
at each original leaf occurrence and then assembling the resulting forest. Root wires
are unchanged. The leaf correspondence transports the substituted configuration's named
matching without changing any leaf name. The comparison includes cell labels, external
interface order and closed-wire counts.

This describes substitution in the remaining configuration. A wire-elimination proof must
additionally identify this assembly with removal of the variable equation from the original
configuration's graph.

## Main definitions

* {lit}`Config.substitutionForest` — original fragments with replacement graphs attached.
* {lit}`Config.substGraphAssemblyIso` — graph compilation agrees with that forest's assembly.

## Main statements

* {lit}`Config.unique_graphLeaf_of_count_one` — wire elimination selects one remaining occurrence.
* {lit}`Config.elimination_inserted_cells` — that occurrence inserts one copy of the replacement.
* {lit}`Config.elimination_cells` — the full substitution retains the context's other cells.

## Tags

interaction net, compiler, configuration, substitution, forest, attachment, graph
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- The wire-elimination side condition selects exactly one leaf in the remaining graph forest. -/
theorem unique_graphLeaf_of_count_one (c : Config arity) (x : ℕ) (count : c.names.count x = 1) :
    ∃! p : c.GraphLeaf, c.graphLeafName p = x := by
  let ends := c.graphLeafOrder.filter fun p ↦ decide (c.graphLeafName p = x)
  have hc : (c.graphLeafOrder.map c.graphLeafName).count x = ends.length := by
    simp only [List.count, List.countP_eq_length_filter, List.filter_map, List.length_map]
    rfl
  have hl : ends.length = 1 := hc.symm.trans ((c.graphLeaf_count x).trans count)
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hl
  have hm (q : c.GraphLeaf) : q ∈ ends ↔ c.graphLeafName q = x := by
    have cover := TermFragment.forestOrder_cover c.graphRootOrder c.graphRootOrder_cover
      c.graphFragments q
    change q ∈ c.graphLeafOrder at cover
    simp only [ends, List.mem_filter, cover, decide_eq_true_eq, true_and]
  refine ⟨p, (hm p).mp ?_, fun q hq ↦ ?_⟩
  · rw [hp]
    exact List.mem_singleton_self p
  · have h := (hm q).mpr hq
    rw [hp, List.mem_singleton] at h
    exact h

/-- Eliminating a once-occurring name inserts one copy of its replacement, preserving symbols. -/
theorem elimination_inserted_cells (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (count : c.names.count x = 1) :
    ∃ e : (Σ q : c.GraphLeaf,
      (if c.graphLeafName q = x then t else Term.var (c.graphLeafName q)).fragment.Cell) ≃
        t.fragment.Cell, ∀ q, t.fragment.label (e q) =
      (if c.graphLeafName q.1 = x then t else Term.var (c.graphLeafName q.1)).fragment.label
        q.2 := by
  obtain ⟨p, hp, unique⟩ := c.unique_graphLeaf_of_count_one x count
  let select (q : Σ q : c.GraphLeaf,
      (if c.graphLeafName q = x then t else Term.var (c.graphLeafName q)).fragment.Cell) :
      t.fragment.Cell :=
    if h : c.graphLeafName q.1 = x then Term.fragmentCellEquiv (ite_eq_left h) q.2
    else Fin.elim0 (Term.fragmentCellEquiv (ite_eq_right h) q.2)
  let insert (v : t.fragment.Cell) : Σ q : c.GraphLeaf,
      (if c.graphLeafName q = x then t else Term.var (c.graphLeafName q)).fragment.Cell :=
    ⟨p, (Term.fragmentCellEquiv (ite_eq_left hp)).symm v⟩
  refine ⟨⟨select, insert, ?_, ?_⟩, ?_⟩
  · rintro ⟨q, v⟩
    by_cases hq : c.graphLeafName q = x
    · have he := unique q hq
      subst q
      dsimp only [select]
      rw [dite_eq_left hp]
      apply congrArg (Sigma.mk p)
      exact (Term.fragmentCellEquiv (ite_eq_left hp)).symm_apply_apply v
    · exact Fin.elim0 (Term.fragmentCellEquiv (ite_eq_right hq) v)
  · intro v
    dsimp only [select, insert]
    rw [dite_eq_left hp]
    exact (Term.fragmentCellEquiv (ite_eq_left hp)).apply_symm_apply v
  · rintro ⟨q, v⟩
    change t.fragment.label (select ⟨q, v⟩) = _
    by_cases hq : c.graphLeafName q = x
    · dsimp only [select]
      rw [dite_eq_left hq]
      exact Term.fragment_label_cast (ite_eq_left hq) v
    · exact Fin.elim0 (Term.fragmentCellEquiv (ite_eq_right hq) v)

/-- Attach the appropriate replacement graph at each leaf of every original root term. -/
def substitutionForest (σ : ℕ → Term arity ℕ) (c : Config arity) :
    c.GraphRoot → TermFragment arity ℕ :=
  fun i ↦ (c.graphFragments i).attach (fun p ↦ (σ ((c.graphFragments i).name p)).fragment)

/-- A root in the substituted configuration corresponds to attachment at its original root. -/
def substFragmentCorrespondence (σ : ℕ → Term arity ℕ) (c : Config arity)
    (i : (c.subst σ).GraphRoot) :
    TermFragment.Renaming id ((c.subst σ).graphFragments i)
      (c.substitutionForest σ ((c.substRootEquiv σ).symm i)) := by
  have h := c.graphFragments_subst σ ((c.substRootEquiv σ).symm i)
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  dsimp only [substitutionForest]
  rw [graphFragments_term]
  exact Term.substitutionCorrespondence σ (c.graphTerm ((c.substRootEquiv σ).symm i))

/-- Substituting a configuration retains its cells and inserts the cells at its leaf occurrences. -/
def substCellsEquiv (σ : ℕ → Term arity ℕ) (c : Config arity) :
    (c.subst σ).GraphCell ≃ c.GraphCell ⊕
      (Σ p : c.GraphLeaf, (σ (c.graphLeafName p)).fragment.Cell) :=
  (familyEquiv (c.substRootEquiv σ).symm
    (fun i ↦ (c.substFragmentCorrespondence σ i).cells)).trans
      ((Equiv.sigmaSumDistrib (fun i ↦ (c.graphFragments i).Cell)
        (fun i ↦ Σ p : (c.graphFragments i).Leaf,
          (σ ((c.graphFragments i).name p)).fragment.Cell)).trans
          (Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaAssoc
            (fun i (p : (c.graphFragments i).Leaf) ↦
              (σ ((c.graphFragments i).name p)).fragment.Cell)).symm))

/-- The complete configuration's substitution bijection preserves retained and inserted symbols. -/
theorem substCellsEquiv_label (σ : ℕ → Term arity ℕ) (c : Config arity)
    (p : (c.subst σ).GraphCell) :
    Sum.elim c.graphLabel
      (fun q : Σ p : c.GraphLeaf, (σ (c.graphLeafName p)).fragment.Cell ↦
        (σ (c.graphLeafName q.1)).fragment.label q.2) (c.substCellsEquiv σ p) =
      (c.subst σ).graphLabel p := by
  rcases p with ⟨i, p⟩
  have hl := (c.substFragmentCorrespondence σ i).labels p
  dsimp [substCellsEquiv, familyEquiv, sigmaCongrRight', Equiv.sigmaSumDistrib]
  cases he : (c.substFragmentCorrespondence σ i).cells p with
  | inl q =>
    rw [he] at hl
    exact hl
  | inr q =>
    rw [he] at hl
    exact hl

/-- Wire elimination's substitution retains every old cell and inserts the replacement once. -/
theorem elimination_cells (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (count : c.names.count x = 1) :
    let σ := fun y ↦ if y = x then t else Term.var y
    ∃ e : (c.subst σ).GraphCell ≃ c.GraphCell ⊕ t.fragment.Cell,
      ∀ p, Sum.elim c.graphLabel t.fragment.label (e p) = (c.subst σ).graphLabel p := by
  intro σ
  obtain ⟨e, he⟩ := c.elimination_inserted_cells x t count
  refine ⟨(c.substCellsEquiv σ).trans (Equiv.sumCongr (Equiv.refl _) e), ?_⟩
  intro p
  have h := c.substCellsEquiv_label σ p
  change Sum.elim _ _ ((Equiv.sumCongr (Equiv.refl _) e) (c.substCellsEquiv σ p)) = _
  cases hp : c.substCellsEquiv σ p with
  | inl q =>
    rw [hp] at h
    exact h
  | inr q =>
    rw [hp] at h
    exact (he q).trans h

/-- Substituted leaves correspond to the replacement leaves at their original occurrences. -/
def substForestLeaves (σ : ℕ → Term arity ℕ) (c : Config arity) :
    (c.subst σ).GraphLeaf ≃ (Σ i, (c.substitutionForest σ i).Leaf) :=
  TermFragment.forestLeafEquiv (c.subst σ).graphFragments (c.substitutionForest σ)
    (c.substRootEquiv σ).symm (fun i ↦ (c.substFragmentCorrespondence σ i).leaves)

/-- The forest correspondence retains the concrete wire name at each replacement leaf. -/
theorem substForestLeaves_name (σ : ℕ → Term arity ℕ) (c : Config arity)
    (p : (c.subst σ).GraphLeaf) :
    (c.substitutionForest σ (c.substForestLeaves σ p).1).name
      (c.substForestLeaves σ p).2 = (c.subst σ).graphLeafName p :=
  (c.substFragmentCorrespondence σ p.1).names p.2

/-- Transport the substituted configuration's named wires to their attachment occurrences. -/
def substForestWiring (σ : ℕ → Term arity ℕ) (c : Config arity)
    (closed : (c.subst σ).Closed) : Wiring (Fin 0 ⊕ (Σ i, (c.substitutionForest σ i).Leaf)) :=
  ((c.subst σ).graphLeafWiring closed).map
    ((c.substForestLeaves σ).trans (PortNet.emptyCellEquiv _).symm)

/-- Assemble the complete substituted graph from original fragments and their attachments. -/
def substGraphAssemblyIso (σ : ℕ → Term arity ℕ) (c : Config arity)
    (closed : (c.subst σ).Closed) :
    (((c.subst σ).toFiniteNet closed).2.2.reboundary (c.substBoundaryEquiv σ).symm).Iso
      ((TermFragment.assemble (c.substitutionForest σ) c.graphRootWiring
        (c.substForestWiring σ closed)).reboundary c.graphBoundaryEquiv) := by
  let d := c.subst σ
  let f := d.graphFragments
  let g := c.substitutionForest σ
  let b := (c.substBoundaryEquiv σ).symm
  let e := (c.substRootEquiv σ).symm
  let h := c.substFragmentCorrespondence σ
  have hr : d.graphRootWiring.map (Equiv.sumCongr b e) = c.graphRootWiring := by
    rw [← c.graphRootWiring_subst σ, ← Wiring.map_trans]
    have he : (Equiv.sumCongr (c.substBoundaryEquiv σ) (c.substRootEquiv σ)).trans
        (Equiv.sumCongr b e) = Equiv.refl _ := by
      ext p
      cases p with
      | inl i => exact congrArg Sum.inl ((c.substBoundaryEquiv σ).symm_apply_apply i)
      | inr i => exact congrArg Sum.inr ((c.substRootEquiv σ).symm_apply_apply i)
    rw [he, Wiring.map_refl]
  have hl : ((d.graphLeafWiring closed).map (PortNet.emptyCellEquiv _).symm).map
      (Equiv.sumCongr (Equiv.refl (Fin 0)) (c.substForestLeaves σ)) =
        c.substForestWiring σ closed := by
    have he : (PortNet.emptyCellEquiv d.GraphLeaf).symm.trans
        (Equiv.sumCongr (Equiv.refl (Fin 0)) (c.substForestLeaves σ)) =
        (c.substForestLeaves σ).trans (PortNet.emptyCellEquiv _).symm := by ext p; rfl
    rw [← Wiring.map_trans, he]
    rfl
  have hi := TermFragment.assembleIsoBoundary f g b e (fun i ↦ (h i).cells)
    (fun i ↦ (h i).leaves) (fun i ↦ (h i).labels) (fun i ↦ (h i).wires)
    (fun i ↦ (h i).loops) d.graphRootWiring c.graphRootWiring
    ((d.graphLeafWiring closed).map (PortNet.emptyCellEquiv _).symm)
    (c.substForestWiring σ closed) hr hl
  have hi := hi.reboundary c.graphBoundaryEquiv
  have hb : (Equiv.sumCongr b (Equiv.refl (Fin 0))).trans c.graphBoundaryEquiv =
      d.graphBoundaryEquiv.trans b := by
    ext p
    cases p with
    | inl p => rfl
    | inr p => exact Fin.elim0 p
  rw [PortNet.reboundary_trans, hb, ← PortNet.reboundary_trans] at hi
  exact ((d.occurrenceIndexedIso closed).symm.reboundary b).trans hi

end Geb.InteractionNet.Config

end
