/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigGraphRenaming
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# A configuration's forest and boundary context

A configuration's graph is assembled from the disjoint graphs of its terms and one
surrounding matching. That matching connects equation roots, named leaves and the ordered
external interface. The forest has no closed wires before the context is attached.

## Main definitions

* {lit}`Config.graphForest` — the disjoint graph fragments of a configuration.
* {lit}`Config.graphContextWiring` — the surrounding root and leaf matching.

## Tags

interaction net, compiler, configuration, forest, boundary, assembly
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- Roots and leaves exposed by the configuration's disjoint term fragments. -/
abbrev GraphForestBoundary (c : Config arity) := Σ i, Unit ⊕ (c.graphFragments i).Leaf

/-- Allocate all term fragments before connecting equations or named leaves. -/
def graphForest (c : Config arity) : PortNet arity c.graphLabel c.GraphForestBoundary :=
  PortNet.sigma (fun i ↦ (c.graphFragments i).net)

/-- Term fragments have no closed wire components before their surrounding wires are attached. -/
theorem graphForest_loops (c : Config arity) : c.graphForest.loops = 0 := by
  have hz (i : c.GraphRoot) : (c.graphFragments i).net.loops = 0 := by
    rw [graphFragments_term, Term.fragment_loops]
  simp [graphForest, PortNet.sigma, hz]

/-- Connect all fragment roots and equally named leaves to the ordered external interface. -/
def graphContextWiring (c : Config arity) (closed : c.Closed) :
    Wiring (Fin c.interface.length ⊕ c.GraphForestBoundary) :=
  ((c.graphRootWiring.sum ((c.graphLeafWiring closed).map
    (PortNet.emptyCellEquiv _).symm)).map (TermFragment.assemblyBoundaryEquiv c.graphFragments)).map
      (Equiv.sumCongr c.graphBoundaryEquiv (Equiv.refl _))

/-- Locate the root matching's external positions and fragment roots in the complete context. -/
def graphContextRoot (c : Config arity) :
    Fin c.interface.length ⊕ c.GraphRoot ↪ Fin c.interface.length ⊕ c.GraphForestBoundary :=
  (Function.Embedding.inl.trans
    (TermFragment.assemblyBoundaryEquiv c.graphFragments).toEmbedding).trans
      (Equiv.sumCongr c.graphBoundaryEquiv (Equiv.refl _)).toEmbedding

/-- Locate each named occurrence in the complete boundary context. -/
def graphContextLeaf (c : Config arity) :
    c.GraphLeaf ↪ Fin c.interface.length ⊕ c.GraphForestBoundary :=
  (((PortNet.emptyCellEquiv _).symm.toEmbedding.trans .inr).trans
    (TermFragment.assemblyBoundaryEquiv c.graphFragments).toEmbedding).trans
      (Equiv.sumCongr c.graphBoundaryEquiv (Equiv.refl _)).toEmbedding

/-- Root connections retain their partners inside the complete context. -/
theorem graphContextRoot_respects (c : Config arity) (closed : c.Closed) :
    Wiring.Respects c.graphContextRoot c.graphRootWiring (c.graphContextWiring closed) := by
  let leaves := (c.graphLeafWiring closed).map (PortNet.emptyCellEquiv _).symm
  have h := ((Wiring.respects_inl c.graphRootWiring leaves).trans
    (Wiring.respects_map (TermFragment.assemblyBoundaryEquiv c.graphFragments) _)).trans
      (Wiring.respects_map (Equiv.sumCongr c.graphBoundaryEquiv (Equiv.refl _)) _)
  exact h

/-- Named connections retain their partners inside the complete context. -/
theorem graphContextLeaf_respects (c : Config arity) (closed : c.Closed) :
    Wiring.Respects c.graphContextLeaf (c.graphLeafWiring closed)
      (c.graphContextWiring closed) := by
  have h := (((Wiring.respects_map (PortNet.emptyCellEquiv _).symm
    (c.graphLeafWiring closed)).trans (Wiring.respects_inr c.graphRootWiring _)).trans
      (Wiring.respects_map (TermFragment.assemblyBoundaryEquiv c.graphFragments) _)).trans
        (Wiring.respects_map (Equiv.sumCongr c.graphBoundaryEquiv (Equiv.refl _)) _)
  exact h

/-- Configuration compilation is one attachment of the surrounding matching to the term forest. -/
theorem occurrenceNet_eq_graphForest_couple (c : Config arity) (closed : c.Closed) :
    let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
    let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
    c.occurrenceNet closed = c.graphForest.couple (c.graphContextWiring closed) := by
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  exact (PortNet.couple_reboundary _ _ c.graphBoundaryEquiv).symm

end Geb.InteractionNet.Config

end
