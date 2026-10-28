/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigEliminationContext
public import Geb.Prototypes.InteractionNet.ConfigEliminationForest
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Wire elimination preserves the compiled graph

Textual wire elimination replaces a once-occurring variable by its other endpoint's term.
The source graph cancels the head variable wire; the substituted graph cancels its identity
replacements. Both yield the same forest, attachment wire and surrounding matching. Their
ordered external interfaces, cell symbols, partners and closed-wire counts therefore agree
up to cell indexing.

## Main definitions

* {lit}`Config.eliminationIsoAt` — the graph isomorphism for a specified unique occurrence.

## Main statements

* {lit}`Config.elimination_graph_iso` — eliminating a once-occurring name preserves its graph.

## Tags

interaction net, compiler, elimination, substitution, graph, simulation, isomorphism
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- The substituted graph is the retained forest joined to its one replacement. -/
def eliminationTargetIso (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (closed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    let σ := fun y ↦ if y = x then t else Term.var y
    let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
    let := c.eliminationBoundaryEnum x t p hp unique
    (((c.subst σ).toFiniteNet closed).2.2.reboundary (c.substBoundaryEquiv σ).symm).Iso
      ((c.eliminationJoinedForest x t p hp unique).couple
        (c.eliminationContextWiring x t p hp unique closed)) := by
  let σ := fun y ↦ if y = x then t else Term.var y
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := c.eliminationBoundaryEnum x t p hp unique
  let := sigmaEnum (C := fun i ↦ ((c.graphFragments i).attach
    (c.eliminationFragments x t i)).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ ((c.graphFragments i).attach
    (c.eliminationFragments x t i)).Leaf)
  let n := PortNet.sigma (fun i ↦ ((c.graphFragments i).attach
    (c.eliminationFragments x t i)).net)
  have hc := PortNet.coupleIso n (c.eliminationJoinedForest x t p hp unique)
    (c.eliminationAssemblyContextWiring x t closed)
    (c.eliminationContextWiring x t p hp unique closed)
    (c.eliminationForestBoundaryEquiv x t p hp unique)
    (c.eliminationForestCellsEquiv x t p hp unique)
    (c.eliminationForestCellsEquiv_label x t p hp unique)
    (c.eliminationForest_wiring x t p hp unique)
    (c.eliminationForest_loops x t p hp unique)
    (c.eliminationAssemblyContext_wiring x t p hp unique closed)
  have hs := c.substGraphAssemblyIso σ closed
  change PortNet.Iso _ ((n.couple ((c.graphRootWiring.sum (c.substForestWiring σ closed)).map
    (TermFragment.assemblyBoundaryEquiv (c.substitutionForest σ)))).reboundary
      c.graphBoundaryEquiv) at hs
  rw [← PortNet.couple_reboundary] at hs
  exact hs.trans hc

/-- Cancelling the source variable exposes the same joined forest and surrounding matching. -/
def eliminationSourceIso (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (sourceClosed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed)
    (targetClosed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
    let := c.eliminationBoundaryEnum x t p hp unique
    (({ c with equations := (Term.var x, t) :: c.equations } :
      Config arity).occurrenceNet sourceClosed).Iso
        ((c.eliminationJoinedForest x t p hp unique).couple
          (c.eliminationContextWiring x t p hp unique targetClosed)) := by
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  let := c.eliminationBoundaryEnum x t p hp unique
  let := boolEnum
  let n := t.fragment.net.sum c.graphForest
  let e := c.eliminationOpenBoundaryEquiv x t p hp unique
  let w := c.eliminationContextWiring x t p hp unique targetClosed
  have h := PortNet.coupleIso n (n.reboundary e)
    (Wiring.closeWire (c.variableContextWiring x t sourceClosed)).1
    ((Wiring.wire.sum w).map (PortNet.wireBoundaryEquiv _ _))
    e (Equiv.refl _) (fun _ ↦ rfl) rfl rfl
    (c.eliminationOpenContext_wiring x t p hp unique sourceClosed targetClosed)
  rw [← PortNet.couple_closePair, PortNet.couple_closePair_eq] at h
  exact (c.variableEquationIso x t sourceClosed).trans h

/-- The specified unique occurrence identifies the source and substituted finite graphs. -/
def eliminationIsoAt (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (sourceClosed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed)
    (targetClosed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    let σ := fun y ↦ if y = x then t else Term.var y
    (({ c with equations := (Term.var x, t) :: c.equations } :
      Config arity).toFiniteNet sourceClosed).2.2.Iso
        (((c.subst σ).toFiniteNet targetClosed).2.2.reboundary (c.substBoundaryEquiv σ).symm) := by
  let d : Config arity := { c with equations := (Term.var x, t) :: c.equations }
  exact ((d.occurrenceIndexedIso sourceClosed).symm.trans
    (eliminationSourceIso c x t p hp unique sourceClosed targetClosed)).trans
      (eliminationTargetIso c x t p hp unique targetClosed).symm

/-- Substitution for a once-occurring name preserves the complete represented graph. -/
theorem elimination_graph_iso (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (count : c.names.count x = 1)
    (sourceClosed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed)
    (targetClosed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    let σ := fun y ↦ if y = x then t else Term.var y
    Nonempty ((({ c with equations := (Term.var x, t) :: c.equations } :
      Config arity).toFiniteNet sourceClosed).2.2.Iso
        (((c.subst σ).toFiniteNet targetClosed).2.2.reboundary (c.substBoundaryEquiv σ).symm)) := by
  obtain ⟨p, hp, unique⟩ := c.unique_graphLeaf_of_count_one x count
  exact ⟨c.eliminationIsoAt x t p hp unique sourceClosed targetClosed⟩

end Geb.InteractionNet.Config

end
