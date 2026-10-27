/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigAgentPairContext
public import Geb.Prototypes.InteractionNet.ConfigInteractionLeaves
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The unchanged context of an interaction

Removing the head agent equation removes exactly its root wire. All other root connections
and all named leaf connections remain. This decomposition identifies the surrounding
matching independently of the two cells that graph contraction removes.

## Main statements

* {lit}`Config.agentPairContextWiring_eq` — the context consists of old roots and named leaves.

## Tags

interaction net, compiler, context, root, leaf, named wiring
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- Arrange unchanged roots and separated argument and context leaves around the exposed forest. -/
def agentPairContextEquiv (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    (Fin c.interface.length ⊕ c.GraphRoot) ⊕
      ({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
        Config arity).GraphLeaf ≃ Fin c.interface.length ⊕ c.AgentPairBoundary xs ys :=
  let e : (Fin c.interface.length ⊕ c.GraphRoot) ⊕
      ((Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf) ⊕ c.GraphLeaf) ≃
        Fin c.interface.length ⊕ c.AgentPairBoundary xs ys :=
    { toFun := fun p ↦ match p with
        | .inl (.inl i) => .inl i
        | .inl (.inr i) => .inr (.inr ⟨i, .inl ()⟩)
        | .inr (.inl q) => .inr (.inl q)
        | .inr (.inr ⟨i, q⟩) => .inr (.inr ⟨i, .inr q⟩)
      invFun := fun p ↦ match p with
        | .inl i => .inl (.inl i)
        | .inr (.inl q) => .inr (.inl q)
        | .inr (.inr ⟨i, .inl _⟩) => .inl (.inr i)
        | .inr (.inr ⟨i, .inr q⟩) => .inr (.inr ⟨i, q⟩)
      left_inv := by rintro ((i | i) | (q | ⟨i, q⟩)) <;> rfl
      right_inv := by rintro (i | (q | ⟨i, u | q⟩)) <;> rfl }
  (Equiv.sumCongr (Equiv.refl _) (c.agentPairLeafEquiv xs ys).symm).trans e

private def contextEquiv (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    Fin c.interface.length ⊕ ({ c with equations :=
      (Term.agent a xs, Term.agent b ys) :: c.equations } : Config arity).GraphForestBoundary ≃
        Bool ⊕ (Fin c.interface.length ⊕ c.AgentPairBoundary xs ys) :=
  (Equiv.sumCongr (Equiv.refl _) (c.headOccurrencesEquiv
    (Term.agent a xs, Term.agent b ys) (fun f ↦ Unit ⊕ f.Leaf))).symm.trans
      ((Equiv.sumCongr (Equiv.refl _) (c.agentPairRootsEquiv xs ys)).trans
        (PortNet.wireBoundaryEquiv _ _).symm)

private theorem contextEquiv_wiring (c : Config arity)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (closed : ({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).Closed) :
    let := c.agentPairBoundaryEnum xs ys
    (Wiring.closeWire ((({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).graphContextWiring closed).map
        (contextEquiv c xs ys))).1 = c.agentPairContextWiring xs ys closed := by
  let := c.agentPairBoundaryEnum xs ys
  dsimp only [agentPairContextWiring, headContextWiring]
  rw [← Wiring.map_trans]
  rfl

private def oldRoots (c : Config arity) (e : Equation arity ℕ) :
    c.GraphRoot ↪ ({ c with equations := e :: c.equations } : Config arity).GraphRoot :=
  Function.Embedding.sumMap (.refl _) ((Fin.succEmb _).sumMap (Fin.succEmb _))

private theorem roots_respects (c : Config arity)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (closed : ({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).Closed) :
    Wiring.Respects (Function.Embedding.inl.trans (c.agentPairContextEquiv xs ys).toEmbedding)
      c.graphRootWiring (c.agentPairContextWiring xs ys closed) := by
  let := c.agentPairBoundaryEnum xs ys
  rw [← contextEquiv_wiring]
  apply Wiring.closeWire_respects_of_inr
  let d : Config arity := { c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations }
  let e := Function.Embedding.sumMap (Function.Embedding.refl (Fin c.interface.length))
    (oldRoots c (Term.agent a xs, Term.agent b ys))
  have h : Wiring.Respects e c.graphRootWiring d.graphRootWiring := by
    rintro (i | (i | (i | i))) <;> rfl
  have he := (h.trans (d.graphContextRoot_respects closed)).trans
    (Wiring.respects_map (contextEquiv c xs ys) (d.graphContextWiring closed))
  intro p
  have hc (q) : contextEquiv c xs ys (d.graphContextRoot (e q)) =
      Sum.inr (c.agentPairContextEquiv xs ys (.inl q)) := by
    rcases q with i | (i | (i | i)) <;> rfl
  have hp := he p
  change (((d.graphContextWiring closed).map (contextEquiv c xs ys)).partner
    (contextEquiv c xs ys (d.graphContextRoot (e p)))) =
      contextEquiv c xs ys (d.graphContextRoot (e (c.graphRootWiring.partner p))) at hp
  rw [hc, hc] at hp
  exact hp

private theorem leaves_respects (c : Config arity)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (closed : ({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).Closed) :
    Wiring.Respects (Function.Embedding.inr.trans (c.agentPairContextEquiv xs ys).toEmbedding)
      (({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
        Config arity).graphLeafWiring closed) (c.agentPairContextWiring xs ys closed) := by
  let := c.agentPairBoundaryEnum xs ys
  rw [← contextEquiv_wiring]
  apply Wiring.closeWire_respects_of_inr
  let d : Config arity := { c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations }
  have he := (d.graphContextLeaf_respects closed).trans
    (Wiring.respects_map (contextEquiv c xs ys) (d.graphContextWiring closed))
  have hc (q : d.GraphLeaf) : contextEquiv c xs ys (d.graphContextLeaf q) =
      Sum.inr (c.agentPairContextEquiv xs ys (.inr q)) := by
    obtain ⟨q, rfl⟩ := (c.agentPairLeafEquiv xs ys).surjective q
    simp only [agentPairContextEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.symm_apply_apply]
    rcases q with ⟨i | i, q⟩ | ⟨i | (i | i), q⟩ <;> rfl
  intro p
  have hp := he p
  change (((d.graphContextWiring closed).map (contextEquiv c xs ys)).partner
    (contextEquiv c xs ys (d.graphContextLeaf p))) =
      contextEquiv c xs ys (d.graphContextLeaf ((d.graphLeafWiring closed).partner p)) at hp
  rw [hc, hc] at hp
  exact hp

/-- Removing the head root wire leaves precisely the unchanged roots and all named connections. -/
theorem agentPairContextWiring_eq (c : Config arity)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (closed : ({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).Closed) :
    (c.graphRootWiring.sum (({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).graphLeafWiring closed)).map
        (c.agentPairContextEquiv xs ys) = c.agentPairContextWiring xs ys closed := by
  have h : Wiring.Respects (c.agentPairContextEquiv xs ys).toEmbedding
      (c.graphRootWiring.sum (({ c with equations := (Term.agent a xs, Term.agent b ys) ::
        c.equations } : Config arity).graphLeafWiring closed))
          (c.agentPairContextWiring xs ys closed) := by
    rintro (p | q)
    · exact roots_respects c xs ys closed p
    · exact leaves_respects c xs ys closed q
  exact h.map_eq (Wiring.respects_refl _) _ (fun _ ↦ rfl)

end Geb.InteractionNet.Config

end
