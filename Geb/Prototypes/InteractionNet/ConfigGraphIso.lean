/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigGraph
public import Geb.Prototypes.InteractionNet.ForestIso
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Configuration graph invariance under occurrence renaming

The graph compiler's cell indices are an implementation detail. Its interpretation can
first be expressed using syntax occurrence positions, then indexed by finite ordinals.
Corresponding root wires and term fragments determine isomorphic assembled configurations
whenever the occurrence correspondence preserves equal wire names.

## Main definitions

* {lit}`Config.occurrenceNet` — the configuration graph before finite ordinal indexing.
* {lit}`Config.occurrenceIso` — graph invariance under compatible occurrence bijections.

## Tags

interaction net, compiler, configuration, occurrence, isomorphism, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- A graph cell retains the root and internal position of its syntax occurrence. -/
abbrev GraphCell (c : Config arity) := Σ i, (c.graphFragments i).Cell

/-- Each graph occurrence carries the symbol of its original syntax cell. -/
def graphLabel (c : Config arity) (p : c.GraphCell) : α := (c.graphFragments p.1).label p.2

/-- Remove the empty leaf-boundary summand without reordering the interface. -/
def graphBoundaryEquiv (c : Config arity) : Fin c.interface.length ⊕ Fin 0 ≃
    Fin c.interface.length :=
  (Equiv.sumComm _ (Fin 0)).trans (PortNet.emptyCellEquiv _)

/-- Assemble a configuration while retaining its structural cell occurrence positions. -/
def occurrenceNet (c : Config arity) (closed : c.Closed) :
    PortNet arity c.graphLabel (Fin c.interface.length) :=
  (TermFragment.assemble c.graphFragments c.graphRootWiring
    ((c.graphLeafWiring closed).map (PortNet.emptyCellEquiv _).symm)).reboundary
      c.graphBoundaryEquiv

/-- The executable finite graph is exactly an indexing of its occurrence presentation. -/
def occurrenceIndexedIso (c : Config arity) (closed : c.Closed) :
    (c.occurrenceNet closed).Iso (c.toFiniteNet closed).2.2 :=
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  PortNet.indexedIso (c.occurrenceNet closed)

/-- Corresponding name classes determine identical leaf matchings under an occurrence bijection. -/
theorem graphLeafWiring_map (c d : Config arity) (hc : c.Closed) (hd : d.Closed)
    (e : c.GraphLeaf ≃ d.GraphLeaf)
    (names : ∀ p q, c.graphLeafName p = c.graphLeafName q →
      d.graphLeafName (e p) = d.graphLeafName (e q)) :
    (c.graphLeafWiring hc).map e = d.graphLeafWiring hd := by
  let := c.graphLeafEnum
  let := d.graphLeafEnum
  have h := Wiring.ofNames_respects c.graphLeafOrder
    (TermFragment.forestOrder_unique _ c.graphRootOrder_unique c.graphFragments)
    (TermFragment.forestOrder_cover _ c.graphRootOrder_cover c.graphFragments)
    c.graphLeafName (c.graphLeaf_two hc) d.graphLeafOrder
    (TermFragment.forestOrder_unique _ d.graphRootOrder_unique d.graphFragments)
    (TermFragment.forestOrder_cover _ d.graphRootOrder_cover d.graphFragments)
    d.graphLeafName (d.graphLeaf_two hd) e.toEmbedding names
  exact h.map_eq (Wiring.respects_refl _) e (fun _ ↦ rfl)

/-- Compatible root, cell and leaf occurrence bijections preserve the assembled graph. -/
def occurrenceIso (c d : Config arity) (hc : c.Closed) (hd : d.Closed)
    (b : Fin c.interface.length ≃ Fin d.interface.length) (e : c.GraphRoot ≃ d.GraphRoot)
    (cells : ∀ i, (c.graphFragments i).Cell ≃ (d.graphFragments (e i)).Cell)
    (leaves : ∀ i, (c.graphFragments i).Leaf ≃ (d.graphFragments (e i)).Leaf)
    (labels : ∀ i p, (d.graphFragments (e i)).label (cells i p) = (c.graphFragments i).label p)
    (wires : ∀ i, (c.graphFragments i).net.wiring.map (endpointEquiv arity
      (Equiv.sumCongr (Equiv.refl Unit) (leaves i)) (cells i) (labels i)) =
        (d.graphFragments (e i)).net.wiring)
    (loops : ∀ i, (c.graphFragments i).net.loops = (d.graphFragments (e i)).net.loops)
    (roots : c.graphRootWiring.map (Equiv.sumCongr b e) = d.graphRootWiring)
    (names : ∀ p q, c.graphLeafName p = c.graphLeafName q →
      d.graphLeafName (TermFragment.forestLeafEquiv c.graphFragments d.graphFragments e leaves p) =
        d.graphLeafName
          (TermFragment.forestLeafEquiv c.graphFragments d.graphFragments e leaves q)) :
    ((c.occurrenceNet hc).reboundary b).Iso (d.occurrenceNet hd) := by
  let l := TermFragment.forestLeafEquiv c.graphFragments d.graphFragments e leaves
  have hw := graphLeafWiring_map c d hc hd l names
  have hl : ((c.graphLeafWiring hc).map (PortNet.emptyCellEquiv _).symm).map
      (Equiv.sumCongr (Equiv.refl (Fin 0)) l) =
        (d.graphLeafWiring hd).map (PortNet.emptyCellEquiv _).symm := by
    have he : (PortNet.emptyCellEquiv c.GraphLeaf).symm.trans
        (Equiv.sumCongr (Equiv.refl (Fin 0)) l) =
        l.trans (PortNet.emptyCellEquiv d.GraphLeaf).symm := by ext p; rfl
    rw [← Wiring.map_trans, he, Wiring.map_trans, hw]
  have h := TermFragment.assembleIsoBoundary c.graphFragments d.graphFragments b e
    cells leaves labels wires loops c.graphRootWiring d.graphRootWiring
    ((c.graphLeafWiring hc).map (PortNet.emptyCellEquiv _).symm)
    ((d.graphLeafWiring hd).map (PortNet.emptyCellEquiv _).symm) roots hl
  have hi := h.reboundary d.graphBoundaryEquiv
  have hb : (Equiv.sumCongr b (Equiv.refl (Fin 0))).trans d.graphBoundaryEquiv =
      c.graphBoundaryEquiv.trans b := by
    ext p
    cases p with
    | inl p => rfl
    | inr p => exact Fin.elim0 p
  rw [PortNet.reboundary_trans, hb, ← PortNet.reboundary_trans] at hi
  exact hi

/-- An occurrence isomorphism also relates the finite graphs used by the runtime. -/
def indexedIso (c d : Config arity) (hc : c.Closed) (hd : d.Closed)
    (b : Fin c.interface.length ≃ Fin d.interface.length)
    (h : ((c.occurrenceNet hc).reboundary b).Iso (d.occurrenceNet hd)) :
    ((c.toFiniteNet hc).2.2.reboundary b).Iso (d.toFiniteNet hd).2.2 :=
  ((c.occurrenceIndexedIso hc).symm.reboundary b).trans
    (h.trans (d.occurrenceIndexedIso hd))

end Geb.InteractionNet.Config

end
