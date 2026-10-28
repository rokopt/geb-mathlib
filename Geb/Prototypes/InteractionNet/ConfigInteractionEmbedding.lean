/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigInteractionAllocation
public import Geb.Prototypes.InteractionNet.RuleInstantiationCancellation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# A common matching for the two interaction forests

The graph join and the textual attachment can be compared before removing their consumed
endpoints. Both embed into the original rule, argument and context matchings after the
internal variable extensions have been cancelled. Their remaining cuts differ only in
the order of the two endpoints of each argument connection.

## Main definitions

* {lit}`Config.InteractionEndpoint` — the common endpoint allocation.
* {lit}`Config.interactionAttachedEmbedding` — locate the textual forest's live endpoints.
* {lit}`Config.interactionJoinInput` — locate the two inputs of graph joining.

## Main statements

* {lit}`Config.interactionAttached_spec` — the attached forest embeds in the common matching.
* {lit}`Config.interactionJoined_spec` — the joined forest embeds in the same matching.

## Tags

interaction net, graph, compiler, attachment, joining, embedding
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- Original rule and replacement endpoints beside the untouched context forest. -/
abbrev InteractionEndpoint (c : Config arity) (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  r.InstantiationEndpoint xs ys ⊕ Endpoint arity c.graphLabel c.GraphForestBoundary

/-- Compare common endpoints using the explicit finite indices of their fragments. -/
@[instance_reducible] def interactionEndpointDecidableEq (c : Config arity)
    (r : Rule arity a b) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) : DecidableEq (c.InteractionEndpoint r xs ys) :=
  let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
  let : DecidableEq c.GraphCell := sigmaEnum.decEq
  let : DecidableEq c.GraphForestBoundary := sigmaEnum.decEq
  inferInstance

/-- The matching after cancelling all internal variable extensions. -/
def interactionMatching (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Wiring (c.InteractionEndpoint r xs ys) :=
  ((r.instantiationWiring xs ys).map (r.internalRelocate linear xs ys)).sum c.graphForest.wiring

/-- The argument attachment cuts, embedded beside the unaffected context. -/
def interactionPorts (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Boundary arity a b × Bool ↪ c.InteractionEndpoint r xs ys :=
  (r.argumentPorts linear xs ys).trans .inl

/-- Locate the textual attachment forest and the surrounding forest in the common allocation. -/
def interactionAttachedEmbedding (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (next : ℕ) (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  (PortNet.sumEndpointEquiv arity
    (TermFragment.attachedForestLabel (EquationGraph.fragments r.equations)
      (r.instantiationFragments next xs ys)) c.graphLabel
        (TermFragment.AttachedForestBoundary (EquationGraph.fragments r.equations)
          (r.instantiationFragments next xs ys)) c.GraphForestBoundary).symm.toEmbedding.trans
            ((r.instantiationForestEmbedding linear next xs ys).sumMap (.refl _))

/-- Undo the endpoint collection and boundary reordering of the exposed argument context. -/
def interactionBodyEquiv (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :=
  (Equiv.sumCongr (c.agentArgumentsBoundaryEquiv xs ys)
    (Equiv.refl (CellPort arity (c.agentPairLabel xs ys)))).symm.trans
      ((PortNet.sumEndpointEquiv arity
        (fun p : Σ p, (agentArguments xs ys p).Cell ↦ (agentArguments xs ys p.1).label p.2)
        c.graphLabel (Σ p, Unit ⊕ (agentArguments xs ys p).Leaf)
        c.GraphForestBoundary).symm.trans
          (Equiv.sumCongr (PortNet.sigmaEndpointEquiv arity
            (fun p ↦ (agentArguments xs ys p).label)).symm (Equiv.refl _)))

/-- Undo the rule forest's endpoint collection and exposure of external leaf occurrences. -/
def interactionRuleEquiv (r : Rule arity a b) (linear : r.Linear) :=
  (Equiv.sumCongr (r.openBoundaryEquiv linear)
    (Equiv.refl (CellPort arity (fun p : Σ i, (EquationGraph.fragments r.equations i).Cell ↦
      (EquationGraph.fragments r.equations p.1).label p.2)))).symm.trans
        (PortNet.sigmaEndpointEquiv arity
          (fun i ↦ (EquationGraph.fragments r.equations i).label)).symm

/-- Place argument, context and rule endpoints into the common allocation. -/
def interactionPlacement (c : Config arity) (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    ((Σ p : Boundary arity a b, Endpoint arity (Sum.elim xs ys p).fragment.label
      (Unit ⊕ (Sum.elim xs ys p).fragment.Leaf)) ⊕
        Endpoint arity c.graphLabel c.GraphForestBoundary) ⊕
          (Σ i, Endpoint arity (EquationGraph.fragments r.equations i).label
            (Unit ⊕ (EquationGraph.fragments r.equations i).Leaf)) ↪
              c.InteractionEndpoint r xs ys where
  toFun p := match p with
    | .inl (.inl p) => .inl (.inr (.inl p))
    | .inl (.inr p) => .inr p
    | .inr p => .inl (.inl p)
  inj' := by rintro ((p | p) | p) ((q | q) | q) h <;> simp_all

/-- Locate graph joining's inputs after moving the rule's internal leaves to their free ends. -/
def interactionJoinInput (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  (Equiv.sumCongr (c.interactionBodyEquiv xs ys) (interactionRuleEquiv r linear)).toEmbedding.trans
    ((c.interactionPlacement r xs ys).trans
      (Equiv.sumCongr (r.internalRelocate linear xs ys) (Equiv.refl _)).toEmbedding)

/-- The textual attachment embeds into the common matching after all argument cuts. -/
theorem interactionAttached_spec (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (next : ℕ) (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    let : DecidableEq (c.InteractionEndpoint r xs ys) := c.interactionEndpointDecidableEq r xs ys
    let g := Wiring.glue (c.interactionPorts r linear xs ys) (FinEnum.toList _)
      (c.interactionMatching r linear xs ys, 0)
    Wiring.Respects (c.interactionAttachedEmbedding r linear next xs ys)
      (c.interactionAttachedForest r next xs ys).wiring g.1 ∧
        (c.interactionAttachedForest r next xs ys).loops = g.2 := by
  let : DecidableEq (r.InstantiationEndpoint xs ys) := r.instantiationDecidableEq xs ys
  let : DecidableEq c.GraphCell := sigmaEnum.decEq
  let : DecidableEq c.GraphForestBoundary := sigmaEnum.decEq
  have h := r.instantiationForest_after_internal linear next xs ys
  have hg := Wiring.glue_sum_left (r.argumentPorts linear xs ys) (FinEnum.toList _)
    ((r.instantiationWiring xs ys).map (r.internalRelocate linear xs ys), 0)
      c.graphForest.wiring 0
  change Wiring.glue (c.interactionPorts r linear xs ys) (FinEnum.toList _)
    (c.interactionMatching r linear xs ys, 0) = _ at hg
  dsimp only
  rw [hg]
  constructor
  · exact (Wiring.respects_map_symm _ _).trans (h.1.sum (Wiring.respects_refl _))
  · change _ + c.graphForest.loops = _ + 0
    rw [c.graphForest_loops, h.2]

/-- Both inputs of graph joining preserve their original matchings in the common allocation. -/
theorem interactionJoinInput_respects (c : Config arity) (r : Rule arity a b)
    (linear : r.Linear) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    Wiring.Respects (c.interactionJoinInput r linear xs ys)
      ((c.agentPairBody xs ys).wiring.sum (r.openForest linear).wiring)
        (c.interactionMatching r linear xs ys) := by
  have hb : Wiring.Respects (c.interactionBodyEquiv xs ys).toEmbedding
      (c.agentPairBody xs ys).wiring
        ((Wiring.sigma (fun p ↦ (agentArguments xs ys p).net.wiring)).sum
          c.graphForest.wiring) :=
    (Wiring.respects_map_symm _ _).trans ((Wiring.respects_map_symm _ _).trans
      ((Wiring.respects_map_symm _ _).sum (Wiring.respects_refl _)))
  have hr : Wiring.Respects (interactionRuleEquiv r linear).toEmbedding
      (r.openForest linear).wiring
        (Wiring.sigma (fun i ↦ (EquationGraph.fragments r.equations i).net.wiring)) := by
    exact (Wiring.respects_map_symm
      (Equiv.sumCongr (r.openBoundaryEquiv linear) (Equiv.refl _)) _).trans
        (Wiring.respects_map_symm (PortNet.sigmaEndpointEquiv arity
          (fun i ↦ (EquationGraph.fragments r.equations i).label)) _)
  have hp : Wiring.Respects (c.interactionPlacement r xs ys)
      (((Wiring.sigma (fun p ↦ (agentArguments xs ys p).net.wiring)).sum
        c.graphForest.wiring).sum
          (Wiring.sigma (fun i ↦ (EquationGraph.fragments r.equations i).net.wiring)))
      ((r.instantiationWiring xs ys).sum c.graphForest.wiring) := by
    rintro ((p | p) | p) <;> rfl
  exact (hb.sum hr).trans (hp.trans
    ((Wiring.respects_map _ _).sum (Wiring.respects_refl _)))

/-- The two constructions cut the same argument connection with its endpoints reversed. -/
theorem interactionJoin_ports (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (p : Boundary arity a b) (b : Bool) :
    ((PortNet.joinPorts arity _ _ _ _ _).trans
      (c.interactionJoinInput r linear xs ys)) (p, b) =
        c.interactionPorts r linear xs ys (p, !b) := by
  cases b
  · exact congrArg Sum.inl (r.internalRelocate_argument linear xs ys ⟨p, .inl (.inl ())⟩)
  · exact congrArg Sum.inl (r.internalRelocate_external linear xs ys p)

/-- Locate every endpoint retained by graph joining in the common allocation. -/
def interactionJoinedEmbedding (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  (PortNet.joinEmbedding arity _ _ _ _ _).trans (c.interactionJoinInput r linear xs ys)

/-- Graph joining embeds into the same matching and has the same ambient loop count. -/
theorem interactionJoined_spec (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    let : DecidableEq (c.InteractionEndpoint r xs ys) := c.interactionEndpointDecidableEq r xs ys
    let g := Wiring.glue (c.interactionPorts r linear xs ys) (FinEnum.toList _)
      (c.interactionMatching r linear xs ys, 0)
    Wiring.Respects (c.interactionJoinedEmbedding r linear xs ys)
      (c.interactionJoinedForest r linear xs ys).wiring g.1 ∧
        (c.interactionJoinedForest r linear xs ys).loops = g.2 := by
  let : DecidableEq (c.InteractionEndpoint r xs ys) := c.interactionEndpointDecidableEq r xs ys
  let : DecidableEq (c.AgentPairCell xs ys) := (c.agentPairCellEnum xs ys).decEq
  let : DecidableEq (c.AgentPairBoundary xs ys) := (c.agentPairBoundaryEnum xs ys).decEq
  let : DecidableEq (Σ i, (EquationGraph.fragments r.equations i).Cell) := sigmaEnum.decEq
  let : DecidableEq r.ClosedBoundary := r.closedBoundaryEnum.decEq
  have hl : (c.agentPairBody xs ys).loops + (r.openForest linear).loops + 0 = 0 := by
    simp [c.agentPairBody_loops, Rule.openForest, PortNet.reboundary, PortNet.sigma,
      EquationGraph.fragments, Term.fragment_loops]
  have h := (c.agentPairBody xs ys).join_in (r.openForest linear) (FinEnum.toList _)
    FinEnum.nodup_toList FinEnum.mem_toList (c.interactionJoinInput r linear xs ys)
      (c.interactionMatching r linear xs ys, 0)
        (c.interactionJoinInput_respects r linear xs ys) 0 hl
  dsimp only at h ⊢
  rw [Wiring.glue_flip _ _ (c.interactionJoin_ports r linear xs ys)] at h
  exact ⟨h.1, (Nat.add_zero _).symm.trans h.2⟩

end Geb.InteractionNet.Config

end
