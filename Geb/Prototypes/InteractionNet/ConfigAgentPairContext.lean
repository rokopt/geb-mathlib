/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigAgentPairForest
public import Geb.Prototypes.InteractionNet.PairedBoundary
public import Geb.Prototypes.InteractionNet.ContractionCoupling
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Agent interaction inside a configuration's surrounding wires

The graph of a head agent equation is an active pair around its argument forest, attached
to the configuration's remaining matching. Contracting that pair inserts the replacement
at the exposed argument roots. Boundary attachment commutes with this contraction, so
the surrounding matching and all closed-wire components are retained.

## Main definitions

* {lit}`Config.agentPairContextWiring` — the matching outside the head equation's root wire.
* {lit}`Config.agentPairGraphIso` — decompose a compiled head interaction into pair and context.
* {lit}`Config.agentPairResultIso` — contract by insertion at the exposed argument roots.

## Tags

interaction net, compiler, agent, context, contraction, insertion, isomorphism
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- Remove the head equation's paired roots from its surrounding boundary matching. -/
def agentPairContextWiring (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ)
    (closed : ({ c with equations :=
      (Term.agent a xs, Term.agent b ys) :: c.equations } : Config arity).Closed) :
    Wiring (Fin c.interface.length ⊕ c.AgentPairBoundary xs ys) :=
  let := c.agentPairBoundaryEnum xs ys
  Wiring.closeWire ((c.headContextWiring (Term.agent a xs, Term.agent b ys) closed).map
    ((Equiv.sumCongr (Equiv.refl _) (c.agentPairRootsEquiv xs ys)).trans
      (PortNet.wireBoundaryEquiv _ _).symm)) |>.1

/-- The compiled head equation is its reconstructed active pair in the remaining context. -/
def agentPairGraphIso (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ)
    (closed : ({ c with equations :=
      (Term.agent a xs, Term.agent b ys) :: c.equations } : Config arity).Closed) :
    let := c.agentPairCellEnum xs ys
    let := c.agentPairBoundaryEnum xs ys
    (({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
      Config arity).occurrenceNet closed).Iso
        (((c.agentPairBody xs ys).reconstructPair a b).couple
          (c.agentPairContextWiring xs ys closed)) := by
  let := c.agentPairCellEnum xs ys
  let := c.agentPairBoundaryEnum xs ys
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  let := boolEnum
  let eqn := (Term.agent a xs, Term.agent b ys)
  let n := c.headForest eqn
  let e := c.agentPairRootsEquiv xs ys
  let w := (c.headContextWiring eqn closed).map (Equiv.sumCongr (Equiv.refl _) e)
  have h := PortNet.coupleIso n (n.reboundary e) (c.headContextWiring eqn closed) w
    e (Equiv.refl _) (fun _ ↦ rfl) rfl rfl rfl
  have hw : w.partner (.inr (.inl false)) = .inr (.inl true) :=
    congrArg (Equiv.sumCongr (Equiv.refl _) e) (c.headContextWiring_roots eqn closed)
  rw [PortNet.couple_pairedBoundary _ _ hw] at h
  have he : (Wiring.closeWire (w.map (PortNet.wireBoundaryEquiv _ _).symm)).1 =
      c.agentPairContextWiring xs ys closed := by
    dsimp only [w, agentPairContextWiring]
    rw [Wiring.map_trans]
  rw [he] at h
  exact (c.headGraphIso eqn closed).trans
    (h.trans ((c.agentPairForestIso xs ys).couple (c.agentPairContextWiring xs ys closed)))

/-- Contracting the reconstructed pair inserts the rule body at its exposed argument roots. -/
def agentPairResultIso {D : Type} [FinEnum D] {label : D → α}
    (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ)
    (closed : ({ c with equations :=
      (Term.agent a xs, Term.agent b ys) :: c.equations } : Config arity).Closed)
    (rhs : PortNet arity label (Boundary arity a b)) :
    let := c.agentPairCellEnum xs ys
    let := c.agentPairBoundaryEnum xs ys
    let : DecidableEq (c.AgentPairCell xs ys) := FinEnum.decEq
    let : DecidableEq (c.AgentPairBoundary xs ys) := FinEnum.decEq
    let n := (c.agentPairBody xs ys).reconstructPair a b
    let w := c.agentPairContextWiring xs ys closed
    ((n.couple w).contract (n.couple_active w ((c.agentPairBody xs ys).reconstructPair_active a b))
      rhs).Iso ((c.agentPairBody xs ys).plug rhs (FinEnum.toList _)
        FinEnum.nodup_toList FinEnum.mem_toList |>.couple w) := by
  let := c.agentPairCellEnum xs ys
  let := c.agentPairBoundaryEnum xs ys
  let : DecidableEq (c.AgentPairCell xs ys) := FinEnum.decEq
  let : DecidableEq (c.AgentPairBoundary xs ys) := FinEnum.decEq
  let w := c.agentPairContextWiring xs ys closed
  dsimp only
  exact (c.agentPairBody xs ys).reconstructPairCoupleResultIso a b rhs w

end Geb.InteractionNet.Config

end
