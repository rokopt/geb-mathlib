/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigInteractionAssembly
public import Geb.Prototypes.InteractionNet.ConfigInteractionBoundary
public import Geb.Prototypes.InteractionNet.ConfigInteractionContext
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The surrounding matching after interaction

After the forests have been identified, their surrounding matchings consist of the same
four parts: old root connections, old named wires, replacement equation roots and internal
rule wires. Reordering these parts identifies textual assembly with closing the joined
rule and attaching the unchanged context.

## Main statements

* {lit}`Config.interactionAssembly_context` — identify the textual target's surrounding wiring.

## Tags

interaction net, compiler, interaction, context, matching, assembly
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

variable {α : Type} {arity : α → ℕ} {a b : α}

private def contextEquiv (c : Config arity) :
    (Fin c.interface.length ⊕ c.GraphRoot) ⊕ c.GraphLeaf ≃
      Fin c.interface.length ⊕ c.GraphForestBoundary where
  toFun p := match p with
    | .inl (.inl p) => .inl p
    | .inl (.inr i) => .inr ⟨i, .inl ()⟩
    | .inr ⟨i, p⟩ => .inr ⟨i, .inr p⟩
  invFun p := match p with
    | .inl p => .inl (.inl p)
    | .inr ⟨i, .inl _⟩ => .inl (.inr i)
    | .inr ⟨i, .inr p⟩ => .inr ⟨i, p⟩
  left_inv p := by rcases p with (p | i) | ⟨i, p⟩ <;> rfl
  right_inv p := by rcases p with p | ⟨i, u | p⟩ <;> rfl

private def rootsEquiv (c : Config arity) (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Fin c.interface.length ⊕ c.GraphRoot) ⊕ EquationGraph.Root r.equations ≃
      Fin c.interface.length ⊕ ({ c with equations := r.instantiate c.nextName xs ys ++
        c.equations } : Config arity).GraphRoot :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumComm _ _).trans ((Equiv.sumCongr
      (EquationGraph.substRootEquiv (r.argumentSubstitution c.nextName xs ys)
        r.equations).symm (Equiv.refl _)).trans
          (c.appendRootEquiv (r.instantiate c.nextName xs ys)))))

private def rawEquiv (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  (Equiv.sumSumSumComm (Fin c.interface.length ⊕ c.GraphRoot)
    ({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
      Config arity).GraphLeaf (EquationGraph.Root r.equations) r.InternalLeaf).trans
        ((Equiv.sumCongr (rootsEquiv c r xs ys) (c.interactionLeafEquiv r linear xs ys)).trans
          (contextEquiv ({ c with equations := r.instantiate c.nextName xs ys ++ c.equations } :
            Config arity)))

private def joinedEquiv (c : Config arity) (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  (Equiv.sumCongr (c.agentPairContextEquiv xs ys) (Equiv.refl r.ClosedBoundary)).trans
    (Equiv.sumAssoc _ _ _)

private theorem raw_wiring (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (hs : ({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).Closed)
    (ht : ({ c with equations := r.instantiate c.nextName xs ys ++
      c.equations } : Config arity).Closed) :
    ((c.graphRootWiring.sum (({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).graphLeafWiring hs)).sum (r.closedWiring linear)).map
        (rawEquiv c r linear xs ys) =
          ({ c with equations := r.instantiate c.nextName xs ys ++ c.equations } :
            Config arity).graphContextWiring ht := by
  let s : Config arity := { c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations }
  let d : Config arity := { c with equations := r.instantiate c.nextName xs ys ++ c.equations }
  have hr : Wiring.Respects (rootsEquiv c r xs ys).toEmbedding
      (c.graphRootWiring.sum (EquationGraph.rootWiring r.equations)) d.graphRootWiring := by
    rintro ((i | (i | (i | i))) | (i | i)) <;> rfl
  have hl := Wiring.respects_map (c.interactionLeafEquiv r linear xs ys)
    ((s.graphLeafWiring hs).sum (r.internalWiring linear))
  rw [c.interaction_leafWiring r linear xs ys hs ht] at hl
  have hc : Wiring.Respects (contextEquiv d).toEmbedding
      (d.graphRootWiring.sum (d.graphLeafWiring ht)) (d.graphContextWiring ht) := by
    rintro (p | p)
    · have he (q : Fin d.interface.length ⊕ d.GraphRoot) :
          contextEquiv d (.inl q) = d.graphContextRoot q := by cases q <;> rfl
      change (d.graphContextWiring ht).partner (contextEquiv d (.inl p)) =
        contextEquiv d (.inl (d.graphRootWiring.partner p))
      rw [he, he]
      exact d.graphContextRoot_respects ht p
    · exact d.graphContextLeaf_respects ht p
  have hp : Wiring.Respects
      (Equiv.sumSumSumComm (Fin c.interface.length ⊕ c.GraphRoot) s.GraphLeaf
        (EquationGraph.Root r.equations) r.InternalLeaf).toEmbedding
      ((c.graphRootWiring.sum (s.graphLeafWiring hs)).sum (r.closedWiring linear))
      ((c.graphRootWiring.sum (EquationGraph.rootWiring r.equations)).sum
        ((s.graphLeafWiring hs).sum (r.internalWiring linear))) := by
    rintro ((p | p) | (p | p)) <;> rfl
  exact (hp.trans ((hr.sum hl).trans hc)).map_eq (Wiring.respects_refl _)
    (rawEquiv c r linear xs ys) (fun _ ↦ rfl)

private theorem joined_wiring (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (hs : ({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).Closed) :
    ((c.graphRootWiring.sum (({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).graphLeafWiring hs)).sum (r.closedWiring linear)).map
        (joinedEquiv c r xs ys) =
          ((c.agentPairContextWiring xs ys hs).sum (r.closedWiring linear)).map
            (Equiv.sumAssoc _ _ _) := by
  dsimp only [joinedEquiv]
  rw [Wiring.map_trans, Wiring.map_sum, Wiring.map_refl, c.agentPairContextWiring_eq]

private theorem boundary_agreement (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (rawEquiv c r linear xs ys).trans
      (Equiv.sumCongr (Equiv.refl (Fin c.interface.length))
        (c.interactionResultBoundaryEquiv r linear xs ys)) = joinedEquiv c r xs ys := by
  ext p
  rcases p with ((i | i) | p) | (i | q)
  · rfl
  · exact congrArg Sum.inr (c.interactionResultBoundary_old_root r linear xs ys i)
  · obtain ⟨p, rfl⟩ := (c.agentPairLeafEquiv xs ys).surjective p
    have hp : (Equiv.sumCongr (c.agentPairLeafEquiv xs ys).symm
        (Equiv.refl r.InternalLeaf)) (.inl (c.agentPairLeafEquiv xs ys p)) = .inl p :=
      congrArg Sum.inl ((c.agentPairLeafEquiv xs ys).symm_apply_apply p)
    change Sum.inr (c.interactionResultBoundaryEquiv r linear xs ys
      ⟨(c.interactionLeafEquiv r linear xs ys (.inl (c.agentPairLeafEquiv xs ys p))).1,
        .inr (c.interactionLeafEquiv r linear xs ys (.inl (c.agentPairLeafEquiv xs ys p))).2⟩) =
          (Equiv.sumAssoc _ _ _) (.inl (c.agentPairContextEquiv xs ys
            (.inr (c.agentPairLeafEquiv xs ys p))))
    simp only [interactionLeafEquiv, agentPairContextEquiv, Equiv.trans_apply,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_apply_apply]
    erw [hp]
    rcases p with p | p
    · exact congrArg Sum.inr (c.interactionResultBoundary_rule_leaf r linear xs ys (.inl p))
    · exact congrArg Sum.inr (c.interactionResultBoundary_old_leaf r linear xs ys p)
  · exact congrArg Sum.inr (c.interactionResultBoundary_rule_root r linear xs ys i)
  · exact congrArg Sum.inr (c.interactionResultBoundary_rule_leaf r linear xs ys (.inr q))

/-- The textual assembly context is the unchanged outer context and the rule's internal closure. -/
theorem interactionAssembly_context (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (hs : ({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).Closed)
    (ht : ({ c with equations := r.instantiate c.nextName xs ys ++
      c.equations } : Config arity).Closed) :
    (c.interactionAssemblyWiring r xs ys ht).map (Equiv.sumCongr (Equiv.refl _)
      (c.interactionForestBoundaryEquiv r linear c.nextName xs ys)) =
        ((c.agentPairContextWiring xs ys hs).sum (r.closedWiring linear)).map
          (Equiv.sumAssoc _ _ _) := by
  have he : (c.interactionAssemblyWiring r xs ys ht).map (Equiv.sumCongr (Equiv.refl _)
      (c.interactionForestBoundaryEquiv r linear c.nextName xs ys)) =
        (({ c with equations := r.instantiate c.nextName xs ys ++ c.equations } :
          Config arity).graphContextWiring ht).map (Equiv.sumCongr (Equiv.refl _)
            (c.interactionResultBoundaryEquiv r linear xs ys)) := by
    dsimp only [interactionAssemblyWiring, appendContextWiring]
    rw [← Wiring.map_trans, ← Wiring.map_trans]
    congr 1
    ext p
    cases p <;> rfl
  rw [he, ← raw_wiring c r linear xs ys hs ht, ← Wiring.map_trans,
    boundary_agreement, joined_wiring]

end Geb.InteractionNet.Config

end
