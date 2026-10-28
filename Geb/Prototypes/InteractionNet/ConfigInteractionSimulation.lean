/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigInteractionForest
public import Geb.Prototypes.InteractionNet.ConfigInteractionWiring
public import Geb.Prototypes.InteractionNet.JoinClosure
public import Geb.Prototypes.InteractionNet.PartialClosureCoupling
public import Geb.Prototypes.InteractionNet.PlugIso
public import Geb.Prototypes.InteractionNet.GraphConfluence
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Textual interaction simulates graph contraction

The graph of the instantiated textual rule is obtained by inserting the compiled rule at
the argument roots and attaching the unchanged context. Together with the active-pair
decomposition, this identifies one textual interaction with one graph contraction. The
comparison retains the ordered interface and every closed-wire component.

## Main definitions

* {lit}`Config.interactionTargetIso` — the textual target agrees with rule insertion.

## Main statements

* {lit}`System.interaction_graph_step` — the compiled textual target is the graph-step result.

## Tags

interaction net, compiler, interaction, simulation, contraction, graph
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- The textual result compiles to insertion of the rule graph into the exposed argument context. -/
def Config.interactionTargetIso (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (hs : ({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).Closed)
    (ht : ({ c with equations := r.instantiate c.nextName xs ys ++
      c.equations } : Config arity).Closed) :
    let := c.agentPairCellEnum xs ys
    let := c.agentPairBoundaryEnum xs ys
    let : DecidableEq (c.AgentPairCell xs ys) := FinEnum.decEq
    let : DecidableEq (c.AgentPairBoundary xs ys) := FinEnum.decEq
    (({ c with equations := r.instantiate c.nextName xs ys ++ c.equations } :
      Config arity).occurrenceNet ht).Iso
        ((c.agentPairBody xs ys).plug (r.toPortRule linear).2.2 (FinEnum.toList _)
          FinEnum.nodup_toList FinEnum.mem_toList |>.couple
            (c.agentPairContextWiring xs ys hs)) := by
  let := c.agentPairCellEnum xs ys
  let := c.agentPairBoundaryEnum xs ys
  let : DecidableEq (c.AgentPairCell xs ys) := FinEnum.decEq
  let : DecidableEq (c.AgentPairBoundary xs ys) := FinEnum.decEq
  let := sigmaEnum (C := fun i ↦ (EquationGraph.fragments r.equations i).Cell)
  let : DecidableEq (Σ i, (EquationGraph.fragments r.equations i).Cell) := FinEnum.decEq
  let := r.closedBoundaryEnum
  let : DecidableEq r.ClosedBoundary := FinEnum.decEq
  let := sigmaEnum (C := fun i ↦ ((EquationGraph.fragments r.equations i).attach
    (r.instantiationFragments c.nextName xs ys i)).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ ((EquationGraph.fragments r.equations i).attach
    (r.instantiationFragments c.nextName xs ys i)).Leaf)
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  have hf := PortNet.coupleIso (c.interactionAttachedForest r c.nextName xs ys)
    (c.interactionJoinedForest r linear xs ys) (c.interactionAssemblyWiring r xs ys ht)
    (((c.agentPairContextWiring xs ys hs).sum (r.closedWiring linear)).map (Equiv.sumAssoc _ _ _))
    (c.interactionForestBoundaryEquiv r linear c.nextName xs ys)
    (c.interactionForestCellsEquiv r linear c.nextName xs ys)
    (c.interactionForestCellsEquiv_label r linear c.nextName xs ys)
    (c.interactionForest_wiring r linear c.nextName xs ys)
    (c.interactionForest_loops r linear c.nextName xs ys)
    (c.interactionAssembly_context r linear xs ys hs ht)
  have hp := ((PortNet.Iso.refl (c.agentPairBody xs ys)).plug (r.openForestIso linear)
    (FinEnum.toList _) FinEnum.nodup_toList FinEnum.mem_toList).couple
      (c.agentPairContextWiring xs ys hs)
  rw [PortNet.plug_close, PortNet.close_couple] at hp
  exact (c.interactionAssemblyIso r xs ys ht).trans (hf.trans hp.symm)

/-- A closed head interaction gives one graph step to its compiled textual result. -/
theorem System.interaction_graph_step (s : System arity) (linear : s.Linear)
    (oriented : s.Oriented) (c : Config arity) (r : Rule arity a b)
    (rule : s.rule a b = some r) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ)
    (hs : ({ c with equations := (Term.agent a xs, Term.agent b ys) ::
      c.equations } : Config arity).Closed)
    (ht : ({ c with equations := r.instantiate c.nextName xs ys ++
      c.equations } : Config arity).Closed) :
    Graph.Step (s.toPortSystem linear oriented)
      (Graph.ofNet (({ c with equations := (Term.agent a xs, Term.agent b ys) ::
        c.equations } : Config arity).toFiniteNet hs))
      (Graph.ofNet (({ c with equations := r.instantiate c.nextName xs ys ++
        c.equations } : Config arity).toFiniteNet ht)) := by
  let := c.agentPairCellEnum xs ys
  let := c.agentPairBoundaryEnum xs ys
  let : DecidableEq (c.AgentPairCell xs ys) := FinEnum.decEq
  let : DecidableEq (c.AgentPairBoundary xs ys) := FinEnum.decEq
  let source : Config arity :=
    { c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations }
  let target : Config arity :=
    { c with equations := r.instantiate c.nextName xs ys ++ c.equations }
  let n := (c.agentPairBody xs ys).reconstructPair a b
  let w := c.agentPairContextWiring xs ys hs
  let redex : (s.toPortSystem linear oriented).Redex (n.couple w) :=
    { left := .inl ()
      right := .inr (.inl ())
      active := n.couple_active w ((c.agentPairBody xs ys).reconstructPair_active a b)
      rhs := r.toPortRule (linear a b r rule)
      rule_eq := s.toPortSystem_rule linear oriented rule }
  let sourceIso := (c.agentPairGraphIso xs ys hs).symm.trans
    (source.occurrenceIndexedIso hs)
  have resultIso : redex.result.Iso (target.toFiniteNet ht).2.2 :=
    (c.agentPairResultIso xs ys hs (r.toPortRule (linear a b r rule)).2.2).trans
      ((c.interactionTargetIso r (linear a b r rule) xs ys hs ht).symm.trans
        (target.occurrenceIndexedIso ht))
  exact Graph.step_of_net ⟨redex.map sourceIso,
    ⟨(redex.mapIso sourceIso).symm.trans resultIso⟩⟩

end Geb.InteractionNet

end
