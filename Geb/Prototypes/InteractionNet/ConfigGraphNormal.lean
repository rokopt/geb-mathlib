/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigGraphIso
public import Geb.Prototypes.InteractionNet.ConfigGraphRenaming
public import Geb.Prototypes.InteractionNet.CouplingWires
public import Geb.Prototypes.InteractionNet.GraphConfluence
public import Geb.Prototypes.InteractionNet.TermGraphNormal
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Equation-free configurations compile to normal graphs

A cell's principal port in a term fragment meets the fragment root or a parent's auxiliary
port. In a configuration without equations, every root is attached to an external interface
position. The named-leaf wiring therefore cannot create an active pair. This proves graph
normality for the canonical final configurations reached by the sequential calculus.

## Main statements

* {lit}`Config.toFiniteNet_no_active` — an equation-free configuration has no active graph pair.
* {lit}`Config.graph_normal_of_equations_eq_nil` — its graph is normal for every rule table.

## Tags

interaction net, compiler, configuration, normal form, principal port, graph
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

namespace Config

/-- Every configuration fragment inherits the term's root-or-auxiliary principal-wire property. -/
theorem fragment_principal_partner (c : Config arity) (i : c.GraphRoot) :
    ∀ a : (c.graphFragments i).Cell,
      (c.graphFragments i).net.wiring.partner
        (PortNet.principal arity (c.graphFragments i).label a) = .inl (.inl ()) ∨
      ∃ b p, p.val ≠ 0 ∧ (c.graphFragments i).net.wiring.partner
        (PortNet.principal arity (c.graphFragments i).label a) =
          .inr (⟨b, p⟩ : CellPort arity (c.graphFragments i).label) := by
  rw [graphFragments_term]
  exact Term.fragment_principal_partner (c.graphTerm i)

/-- With no equations, the occurrence graph has no principal-to-principal wire. -/
theorem occurrenceNet_no_active (c : Config arity) (closed : c.Closed) (empty : c.equations = [])
    (a b : c.GraphCell) : ¬(c.occurrenceNet closed).Active a b := by
  let f := c.graphFragments
  let n := PortNet.sigma (fun i ↦ (f i).net)
  let leafWires := (c.graphLeafWiring closed).map (PortNet.emptyCellEquiv _).symm
  let w := (c.graphRootWiring.sum leafWires).map (TermFragment.assemblyBoundaryEquiv f)
  let := sigmaEnum (C := fun i ↦ (f i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (f i).Leaf)
  have hn : ¬(n.couple w).Active a b := by
    intro h
    rcases a with ⟨i, a⟩
    have hp := Wiring.map_partner (PortNet.sigmaEndpointEquiv arity (fun i ↦ (f i).label))
      (Wiring.sigma fun i ↦ (f i).net.wiring)
      ⟨i, PortNet.principal arity (f i).label a⟩
    change n.wiring.partner (.inr ⟨⟨i, a⟩, 0⟩) =
      PortNet.sigmaEndpointEquiv arity (fun i ↦ (f i).label)
        ⟨i, (f i).net.wiring.partner (PortNet.principal arity (f i).label a)⟩ at hp
    rcases c.fragment_principal_partner i a with hr | ⟨d, p, hne, hi⟩
    · have hi : n.wiring.partner (.inr ⟨⟨i, a⟩, 0⟩) = .inl ⟨i, .inl ()⟩ := by
        rw [hr] at hp
        exact hp
      rcases i with i | (i | i)
      · have hw : w.partner (.inr ⟨.inl i, .inl ()⟩) = .inl (.inl i) :=
          Wiring.map_partner (TermFragment.assemblyBoundaryEquiv f)
            (c.graphRootWiring.sum leafWires) (.inl (.inr (.inl i)))
        have he := n.couple_external_wire w ⟨⟨.inl i, a⟩, 0⟩ ⟨.inl i, .inl ()⟩ (.inl i) hi hw
        have bad := he.symm.trans h
        cases bad
      · exact Fin.elim0 (Fin.cast (congrArg List.length empty) i)
      · exact Fin.elim0 (Fin.cast (congrArg List.length empty) i)
    · have hi' : n.wiring.partner (.inr ⟨⟨i, a⟩, 0⟩) = .inr ⟨⟨i, d⟩, p⟩ := by
        rw [hi] at hp
        exact hp
      have he := n.couple_internal_wire w ⟨⟨i, a⟩, 0⟩ ⟨⟨i, d⟩, p⟩ hi'
      have bad := he.symm.trans h
      exact hne (congrArg (fun q : CellPort arity c.graphLabel ↦ q.2.val) (Sum.inr.inj bad))
  exact fun h ↦ hn ((n.couple w).reboundary_active_iff c.graphBoundaryEquiv a b |>.mp h)

/-- Finite ordinal indexing preserves the absence of active pairs in an equation-free graph. -/
theorem toFiniteNet_no_active (c : Config arity) (closed : c.Closed) (empty : c.equations = [])
    (a b : Fin (c.toFiniteNet closed).1) : ¬(c.toFiniteNet closed).2.2.Active a b := by
  intro h
  exact c.occurrenceNet_no_active closed empty _ _ ((c.occurrenceIndexedIso closed).symm.active h)

/-- An equation-free closed configuration compiles to a graph normal for every rule table. -/
theorem graph_normal_of_equations_eq_nil (c : Config arity) (closed : c.Closed)
    (empty : c.equations = []) (s : PortSystem arity) :
    Schedule.Normal (Graph.Step s) (Graph.ofNet (c.toFiniteNet closed)) := by
  rintro m ⟨n, k, hn, _, r, _⟩
  obtain ⟨e⟩ := Quotient.exact hn
  exact c.toFiniteNet_no_active closed empty _ _ (e.active r.active)

end Config

end Geb.InteractionNet

end
