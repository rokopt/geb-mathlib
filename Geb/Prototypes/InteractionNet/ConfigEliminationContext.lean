/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigEliminationAllocation
public import Geb.Prototypes.InteractionNet.ConfigVariableEquation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The surrounding wires of a wire elimination

After cancelling the head variable, the context joins the replacement root to the selected
old leaf. Its other root connections and surviving named wires are exactly those of the
substituted configuration. This identifies the boundary context for the joined forest.

## Main definitions

* {lit}`Config.eliminationContextWiring` — root connections and surviving named wires.

## Tags

interaction net, compiler, elimination, substitution, context, matching
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- Connect unchanged roots and the named leaves remaining after substitution. -/
def eliminationContextWiring (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (closed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    Wiring (Fin c.interface.length ⊕ c.EliminationBoundary x t) :=
  (c.graphRootWiring.sum
    (((c.subst (fun y ↦ if y = x then t else Term.var y)).graphLeafWiring closed).map
      (c.eliminationLeavesEquiv x t p hp unique))).map (Equiv.sumAssoc _ _ _)

private abbrev Boundary (c : Config arity) (t : Term arity ℕ) :=
  Fin c.interface.length ⊕ ((Unit ⊕ t.fragment.Leaf) ⊕ c.GraphForestBoundary)

private def contextEquiv (c : Config arity) (x : ℕ) (t : Term arity ℕ) :
    (Fin c.interface.length ⊕ ({ c with equations := (Term.var x, t) :: c.equations } :
      Config arity).GraphForestBoundary) ≃ Bool ⊕ Boundary c t :=
  (Equiv.sumCongr (Equiv.refl _)
    (c.headOccurrencesEquiv (Term.var x, t) (fun f ↦ Unit ⊕ f.Leaf))).symm.trans
      ((Equiv.sumCongr (Equiv.refl _)
        (Equiv.sumCongr Equiv.boolEquivPUnitSumPUnit.symm (Equiv.refl _))).trans
          (PortNet.wireBoundaryEquiv _ _).symm)

private theorem contextEquiv_wiring (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (closed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed) :
    (({ c with equations := (Term.var x, t) :: c.equations } :
      Config arity).graphContextWiring closed).map (contextEquiv c x t) =
        c.variableContextWiring x t closed := by
  erw [contextEquiv, Wiring.map_trans, Wiring.map_trans]
  rfl

private def oldRoots (c : Config arity) (e : Equation arity ℕ) :
    c.GraphRoot ↪ ({ c with equations := e :: c.equations } : Config arity).GraphRoot :=
  Function.Embedding.sumMap (.refl _) ((Fin.succEmb _).sumMap (Fin.succEmb _))

private def rootEmbedding (c : Config arity) (t : Term arity ℕ) :
    Fin c.interface.length ⊕ c.GraphRoot ↪ Boundary c t where
  toFun q := match q with
    | .inl i => .inl i
    | .inr i => .inr (.inr ⟨i, .inl ()⟩)
  inj' := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (Sum.inl.inj h)
    · cases h
    · cases h
    · exact congrArg Sum.inr (congrArg Sigma.fst (Sum.inr.inj (Sum.inr.inj h)))

private theorem roots_respects (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (closed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed) :
    Wiring.Respects ((rootEmbedding c t).trans .inr) c.graphRootWiring
      (c.variableContextWiring x t closed) := by
  let d : Config arity := { c with equations := (Term.var x, t) :: c.equations }
  have hr : Wiring.Respects (Function.Embedding.sumMap (.refl _)
      (oldRoots c (Term.var x, t))) c.graphRootWiring d.graphRootWiring := by
    rintro (i | (i | (i | i))) <;> rfl
  have h := (hr.trans (d.graphContextRoot_respects closed)).trans
    (Wiring.respects_map (contextEquiv c x t) (d.graphContextWiring closed))
  have he : ((Function.Embedding.sumMap (.refl _) (oldRoots c (Term.var x, t))).trans
      d.graphContextRoot).trans (contextEquiv c x t).toEmbedding =
        (rootEmbedding c t).trans .inr := by
    ext q
    rcases q with i | (i | (i | i)) <;> rfl
  rw [he, contextEquiv_wiring] at h
  exact h

private def leafEmbedding (c : Config arity) (x : ℕ) (t : Term arity ℕ) :
    t.fragment.Leaf ⊕ {q : c.GraphLeaf // c.graphLeafName q ≠ x} ↪ Boundary c t where
  toFun q := match q with
    | .inl q => .inr (.inl (.inr q))
    | .inr q => .inr (.inr ⟨q.val.1, .inr q.val.2⟩)
  inj' := by
    rintro (q | ⟨⟨i, q⟩, hq⟩) (r | ⟨⟨j, r⟩, hr⟩) h
    · exact congrArg Sum.inl (Sum.inr.inj (Sum.inl.inj (Sum.inr.inj h)))
    · cases h
    · cases h
    · apply congrArg Sum.inr
      apply Subtype.ext
      have he : i = j := congrArg Sigma.fst (Sum.inr.inj (Sum.inr.inj h))
      subst j
      exact congrArg (Sigma.mk i)
        (Sum.inr.inj (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj (Sum.inr.inj h))).2))

private theorem leaves_respects (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (sourceClosed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed)
    (targetClosed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    Wiring.Respects ((leafEmbedding c x t).trans .inr)
      (((c.subst (fun y ↦ if y = x then t else Term.var y)).graphLeafWiring targetClosed).map
        (c.eliminationLeavesEquiv x t p hp unique)) (c.variableContextWiring x t sourceClosed) := by
  let d : Config arity := { c with equations := (Term.var x, t) :: c.equations }
  have h := (((c.eliminationLeafEmbedding_wiring x t p hp unique sourceClosed targetClosed).trans
    (d.graphContextLeaf_respects sourceClosed)).trans
      (Wiring.respects_map (contextEquiv c x t) (d.graphContextWiring sourceClosed)))
  rw [contextEquiv_wiring] at h
  have he : ((c.eliminationLeafEmbedding x t p hp unique).trans d.graphContextLeaf).trans
      (contextEquiv c x t).toEmbedding =
        (c.eliminationLeavesEquiv x t p hp unique).toEmbedding.trans
          ((leafEmbedding c x t).trans .inr) := by
    ext q
    change contextEquiv c x t (d.graphContextLeaf
      (c.headLeafEquiv (Term.var x, t) (.inr
        ((Function.Embedding.sumMap (.refl _) (.subtype _))
          (c.eliminationLeavesEquiv x t p hp unique q))))) =
      Sum.inr (leafEmbedding c x t (c.eliminationLeavesEquiv x t p hp unique q))
    cases he : c.eliminationLeavesEquiv x t p hp unique q with
    | inl r => rfl
    | inr r =>
      rcases r with ⟨⟨i | (i | i), q⟩, hq⟩ <;> rfl
  rw [he] at h
  have h' := (Wiring.respects_map_symm (c.eliminationLeavesEquiv x t p hp unique) _).trans h
  have he' : (c.eliminationLeavesEquiv x t p hp unique).symm.toEmbedding.trans
      ((c.eliminationLeavesEquiv x t p hp unique).toEmbedding.trans
        ((leafEmbedding c x t).trans .inr)) =
          (leafEmbedding c x t).trans (Function.Embedding.inr (α := Bool)) := by
    ext q
    exact congrArg ((leafEmbedding c x t).trans .inr)
      ((c.eliminationLeavesEquiv x t p hp unique).apply_symm_apply q)
  rw [he'] at h'
  exact h'

private theorem variable_leaf_partner (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (closed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed) :
    (c.variableContextWiring x t closed).partner (.inl true) =
      .inr (.inr (.inr ⟨p.1, .inr p.2⟩)) := by
  let d : Config arity := { c with equations := (Term.var x, t) :: c.equations }
  have h := (d.graphContextLeaf_respects closed).trans
    (Wiring.respects_map (contextEquiv c x t) (d.graphContextWiring closed))
  rw [contextEquiv_wiring] at h
  have hl := h (c.headLeafEquiv (Term.var x, t) (.inl (Term.fragmentVarLeaf x)))
  rw [c.head_variable_partner x t p hp closed] at hl
  rcases p with ⟨i | (i | i), q⟩ <;> exact hl

private def componentsEquiv (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    Bool ⊕ ((Fin c.interface.length ⊕ c.GraphRoot) ⊕
      (t.fragment.Leaf ⊕ {q : c.GraphLeaf // c.graphLeafName q ≠ x})) ≃ Boundary c t :=
  (Equiv.sumCongr (Equiv.refl Bool) (Equiv.sumAssoc _ _ _)).trans
    ((PortNet.wireBoundaryEquiv _ _).trans
      (Equiv.sumCongr (Equiv.refl _) (c.eliminationOpenBoundaryEquiv x t p hp unique)).symm)

private theorem components_root (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) (q : Fin c.interface.length ⊕ c.GraphRoot) :
    componentsEquiv c x t p hp unique (.inr (.inl q)) = rootEmbedding c t q := by
  cases q <;> rfl

private theorem components_leaf (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (q : t.fragment.Leaf ⊕ {q : c.GraphLeaf // c.graphLeafName q ≠ x}) :
    componentsEquiv c x t p hp unique (.inr (.inr q)) = leafEmbedding c x t q := by
  cases q <;> rfl

private theorem components_respects (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (sourceClosed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed)
    (targetClosed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
    Wiring.Respects (componentsEquiv c x t p hp unique).toEmbedding
      (Wiring.wire.sum (c.graphRootWiring.sum
        (((c.subst (fun y ↦ if y = x then t else Term.var y)).graphLeafWiring targetClosed).map
          (c.eliminationLeavesEquiv x t p hp unique))))
      (Wiring.closeWire (c.variableContextWiring x t sourceClosed)).1 := by
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  dsimp only
  have hr := Wiring.closeWire_respects_of_inr (roots_respects c x t sourceClosed)
  have hl := Wiring.closeWire_respects_of_inr
    (leaves_respects c x t p hp unique sourceClosed targetClosed)
  have hw := Wiring.closeWire_partner (c.variableContextWiring x t sourceClosed)
    (c.variableContextWiring_root x t sourceClosed) (variable_leaf_partner c x t p hp sourceClosed)
  rintro (b | (q | q))
  · cases b
    · exact ((Wiring.closeWire (c.variableContextWiring x t sourceClosed)).1.partner_eq_iff.mp
        hw).symm
    · exact hw
  · change (Wiring.closeWire (c.variableContextWiring x t sourceClosed)).1.partner
      (componentsEquiv c x t p hp unique (.inr (.inl q))) =
        componentsEquiv c x t p hp unique (.inr (.inl (c.graphRootWiring.partner q)))
    rw [components_root, components_root]
    exact hr q
  · change (Wiring.closeWire (c.variableContextWiring x t sourceClosed)).1.partner
      (componentsEquiv c x t p hp unique (.inr (.inr q))) =
        componentsEquiv c x t p hp unique (.inr (.inr
          ((((c.subst (fun y ↦ if y = x then t else Term.var y)).graphLeafWiring targetClosed).map
            (c.eliminationLeavesEquiv x t p hp unique)).partner q)))
    rw [components_leaf, components_leaf]
    exact hl q

/-- Cancelling the head variable leaves the selected attachment wire and the substituted context. -/
theorem eliminationOpenContext_wiring (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (sourceClosed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed)
    (targetClosed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
    (Wiring.closeWire (c.variableContextWiring x t sourceClosed)).1.map
      (Equiv.sumCongr (Equiv.refl _) (c.eliminationOpenBoundaryEquiv x t p hp unique)) =
        (Wiring.wire.sum (c.eliminationContextWiring x t p hp unique targetClosed)).map
          (PortNet.wireBoundaryEquiv _ _) := by
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  dsimp only
  have h := (components_respects c x t p hp unique sourceClosed targetClosed).map_eq
    (Wiring.respects_refl _) (componentsEquiv c x t p hp unique) (fun _ ↦ rfl)
  rw [← h, ← Wiring.map_trans]
  have he : (componentsEquiv c x t p hp unique).trans
      (Equiv.sumCongr (Equiv.refl _) (c.eliminationOpenBoundaryEquiv x t p hp unique)) =
        (Equiv.sumCongr (Equiv.refl Bool) (Equiv.sumAssoc _ _ _)).trans
          (PortNet.wireBoundaryEquiv _ _) := by
    ext q
    exact (Equiv.sumCongr (Equiv.refl _)
      (c.eliminationOpenBoundaryEquiv x t p hp unique)).apply_symm_apply _
  rw [he, Wiring.map_trans, Wiring.map_sum, Wiring.map_refl]
  rfl

/-- The original root matching and substituted named matching around the attached forest. -/
def eliminationAssemblyContextWiring (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (closed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    Wiring (Fin c.interface.length ⊕
      (Σ i, Unit ⊕ ((c.graphFragments i).attach (c.eliminationFragments x t i)).Leaf)) :=
  let σ := fun y ↦ if y = x then t else Term.var y
  ((c.graphRootWiring.sum (c.substForestWiring σ closed)).map
    (TermFragment.assemblyBoundaryEquiv (c.substitutionForest σ))).map
      (Equiv.sumCongr c.graphBoundaryEquiv (Equiv.refl _))

/-- Separating the one replacement transports the assembled context to its surviving occurrences. -/
theorem eliminationAssemblyContext_wiring (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (closed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    (c.eliminationAssemblyContextWiring x t closed).map
      (Equiv.sumCongr (Equiv.refl _) (c.eliminationForestBoundaryEquiv x t p hp unique)) =
        c.eliminationContextWiring x t p hp unique closed := by
  let σ := fun y ↦ if y = x then t else Term.var y
  let e := (c.substForestLeaves σ).trans (PortNet.emptyCellEquiv _).symm
  have he : (((Equiv.sumCongr (Equiv.refl (Fin c.interface.length ⊕ c.GraphRoot)) e).trans
      (TermFragment.assemblyBoundaryEquiv (c.substitutionForest σ))).trans
        (Equiv.sumCongr c.graphBoundaryEquiv (Equiv.refl _))).trans
          (Equiv.sumCongr (Equiv.refl _) (c.eliminationForestBoundaryEquiv x t p hp unique)) =
      (Equiv.sumCongr (Equiv.refl _) (c.eliminationLeavesEquiv x t p hp unique)).trans
        (Equiv.sumAssoc _ _ _) := by
    ext q
    rcases q with (i | i) | q
    · rfl
    · rfl
    · cases h : c.substForestLeaves σ q with
      | mk i q =>
        cases q with
        | mk j q => rfl
  have hw : (c.graphRootWiring.sum ((c.subst σ).graphLeafWiring closed)).map
      (Equiv.sumCongr (Equiv.refl _) e) =
        c.graphRootWiring.sum (c.substForestWiring σ closed) := by
    rw [Wiring.map_sum, Wiring.map_refl]
    rfl
  change (((c.graphRootWiring.sum (c.substForestWiring σ closed)).map
    (TermFragment.assemblyBoundaryEquiv (c.substitutionForest σ))).map
      (Equiv.sumCongr c.graphBoundaryEquiv (Equiv.refl _))).map _ = _
  erw [← hw, ← Wiring.map_trans, ← Wiring.map_trans, ← Wiring.map_trans, he,
    Wiring.map_trans, Wiring.map_sum, Wiring.map_refl]
  rfl

end Geb.InteractionNet.Config

end
