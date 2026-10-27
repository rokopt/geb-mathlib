/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigAppendOccurrences
public import Geb.Prototypes.InteractionNet.ConfigHeadOccurrences
public import Geb.Prototypes.InteractionNet.RuleInstantiationLeaves
public import Geb.Prototypes.InteractionNet.RuleInternalWiring
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Named wires after interaction

A linear interaction retains every argument and context leaf and adds the rule's internal
wire occurrences. The occurrence bijection preserves old names and allocates internal names.
When both configurations are closed, their named matchings therefore correspond exactly:
the target matching is the disjoint union of the source matching and the internal rule wires.

## Main definitions

* {lit}`Config.interactionLeafEquiv` — retained and internal occurrences in the textual result.

## Main statements

* {lit}`Config.interaction_leafWiring` — the complete named matching after rule instantiation.

## Tags

interaction net, compiler, rule, substitution, occurrence, named wiring
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- The leaves of an agent equation are precisely the argument leaves and context leaves. -/
def agentPairLeafEquiv (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf) ⊕ c.GraphLeaf ≃
      ({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
        Config arity).GraphLeaf :=
  let e : (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf) ⊕ c.GraphLeaf ≃
      (Term.agent a xs).fragment.Leaf ⊕ ((Term.agent b ys).fragment.Leaf ⊕ c.GraphLeaf) :=
    { toFun := fun p ↦ match p with
        | .inl ⟨.inl i, q⟩ => .inl ⟨i, q⟩
        | .inl ⟨.inr i, q⟩ => .inr (.inl ⟨i, q⟩)
        | .inr q => .inr (.inr q)
      invFun := fun p ↦ match p with
        | .inl ⟨i, q⟩ => .inl ⟨.inl i, q⟩
        | .inr (.inl ⟨i, q⟩) => .inl ⟨.inr i, q⟩
        | .inr (.inr q) => .inr q
      left_inv := by rintro (⟨i | i, q⟩ | q) <;> rfl
      right_inv := by rintro (⟨i, q⟩ | (⟨i, q⟩ | q)) <;> rfl }
  e.trans (c.headLeafEquiv (Term.agent a xs, Term.agent b ys))

/-- Separating argument occurrences from the context preserves their wire names. -/
theorem agentPairLeafEquiv_name (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ)
    (p : (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf) ⊕ c.GraphLeaf) :
    ({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
      Config arity).graphLeafName (c.agentPairLeafEquiv xs ys p) =
        Sum.elim (fun p ↦ (Sum.elim xs ys p.1).fragment.name p.2) c.graphLeafName p := by
  rcases p with ⟨i | i, q⟩ | q
  · exact c.headLeafEquiv_name (Term.agent a xs, Term.agent b ys) (.inl ⟨i, q⟩)
  · exact c.headLeafEquiv_name (Term.agent a xs, Term.agent b ys) (.inr (.inl ⟨i, q⟩))
  · exact c.headLeafEquiv_name (Term.agent a xs, Term.agent b ys) (.inr (.inr q))

private theorem cast_name {f g : TermFragment arity ℕ} (h : g = f) (q : f.Leaf) :
    g.name ((congrArg TermFragment.Leaf h).mpr q) = f.name q := by cases h; rfl

/-- Concatenating equation forests preserves each leaf name. -/
theorem appendOccurrencesEquiv_name (c : Config arity) (es : List (Equation arity ℕ))
    (p : EquationGraph.Leaf es ⊕ c.GraphLeaf) :
    ({ c with equations := es ++ c.equations } : Config arity).graphLeafName
      (c.appendOccurrencesEquiv es (fun f ↦ f.Leaf) p) =
        Sum.elim (EquationGraph.leafName es) c.graphLeafName p := by
  rcases p with ⟨i, q⟩ | ⟨i, q⟩
  · exact cast_name (c.appendRootEquiv_fragment es (.inl i)) q
  · exact cast_name (c.appendRootEquiv_fragment es (.inr i)) q

/-- Retain source leaves and add internal rule occurrences in the instantiated configuration. -/
def interactionLeafEquiv (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    ({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
      Config arity).GraphLeaf ⊕ r.InternalLeaf ≃
        ({ c with equations := r.instantiate c.nextName xs ys ++ c.equations } :
          Config arity).GraphLeaf :=
  (Equiv.sumCongr (c.agentPairLeafEquiv xs ys).symm (Equiv.refl _)).trans
    ((Equiv.sumAssoc _ _ _).trans
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
        ((Equiv.sumAssoc _ _ _).symm.trans
          ((Equiv.sumCongr (r.instantiateLeavesEquiv linear c.nextName xs ys).symm
            (Equiv.refl _)).trans
              (c.appendOccurrencesEquiv (r.instantiate c.nextName xs ys) (fun f ↦ f.Leaf))))))

/-- An interaction retains old names and allocates the names of internal rule occurrences. -/
theorem interactionLeafEquiv_name (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : ({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
      Config arity).GraphLeaf ⊕ r.InternalLeaf) :
    ({ c with equations := r.instantiate c.nextName xs ys ++ c.equations } :
      Config arity).graphLeafName (c.interactionLeafEquiv r linear xs ys p) =
        Sum.elim ({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
          Config arity).graphLeafName
            (fun q ↦ r.allocated c.nextName (r.internalLeafName q)) p := by
  have hr (q) := r.instantiateLeavesEquiv_name linear c.nextName xs ys
    ((r.instantiateLeavesEquiv linear c.nextName xs ys).symm q)
  simp only [Equiv.apply_symm_apply] at hr
  rcases p with p | q
  · obtain ⟨p, rfl⟩ := (c.agentPairLeafEquiv xs ys).surjective p
    simp only [Sum.elim_inl, c.agentPairLeafEquiv_name]
    simp only [interactionLeafEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.symm_apply_apply]
    rcases p with p | p
    · exact (c.appendOccurrencesEquiv_name _ (.inl _)).trans (hr (.inl p)).symm
    · exact c.appendOccurrencesEquiv_name _ (.inr p)
  · exact (c.appendOccurrencesEquiv_name _ (.inl _)).trans (hr (.inr q)).symm

/-- The target's named matching is the source matching together with the internal rule wires. -/
theorem interaction_leafWiring (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (sourceClosed : ({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).Closed)
    (targetClosed : ({ c with equations := r.instantiate c.nextName xs ys ++
      c.equations } : Config arity).Closed) :
    ((({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
      Config arity).graphLeafWiring sourceClosed).sum (r.internalWiring linear)).map
        (c.interactionLeafEquiv r linear xs ys) =
          ({ c with equations := r.instantiate c.nextName xs ys ++ c.equations } :
            Config arity).graphLeafWiring targetClosed := by
  let s : Config arity := { c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations }
  let d : Config arity := { c with equations := r.instantiate c.nextName xs ys ++ c.equations }
  let e := c.interactionLeafEquiv r linear xs ys
  let w := (s.graphLeafWiring sourceClosed).sum (r.internalWiring linear)
  have h : Wiring.Respects e.toEmbedding w (d.graphLeafWiring targetClosed) := by
    intro p
    apply Wiring.ofNames_partner_eq
    · exact fun he ↦ w.fixedPointFree p (e.injective he)
    · change d.graphLeafName (e (w.partner p)) = d.graphLeafName (e p)
      dsimp only [d, e]
      rw [c.interactionLeafEquiv_name, c.interactionLeafEquiv_name]
      rcases p with p | q
      · exact Wiring.ofNames_partner_name _ _ _ s.graphLeafName (s.graphLeaf_two sourceClosed) p
      · exact congrArg (r.allocated c.nextName) (r.internalWiring_name linear q)
  exact h.map_eq (Wiring.respects_refl _) e (fun _ ↦ rfl)

end Geb.InteractionNet.Config

end
