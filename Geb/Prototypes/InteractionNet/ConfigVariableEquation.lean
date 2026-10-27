/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigHeadForest
public import Geb.Prototypes.InteractionNet.TermGraphSum
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Removing a variable equation's wire fragment

A variable at the left of the head equation contributes no cells. Its root meets the
right term's root, while its named end meets the other occurrence of that name. Cancelling
the variable fragment therefore joins these two context endpoints. The right term and
all fragments of the remaining configuration are retained, as is the complete graph's
closed-wire count.

## Main definitions

* {lit}`Config.variableContextWiring` — expose the variable's two context endpoints.
* {lit}`Config.variableEquationIso` — remove its wire fragment inside the complete graph.

## Tags

interaction net, compiler, configuration, variable, equation, cancellation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- Expose a head variable's two ends separately from the retained term forest's boundary. -/
def variableContextWiring (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (closed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed) :
    Wiring (Bool ⊕ (Fin c.interface.length ⊕ ((Unit ⊕ t.fragment.Leaf) ⊕
      c.GraphForestBoundary))) :=
  ((c.headContextWiring (Term.var x, t) closed).map (Equiv.sumCongr (Equiv.refl _)
    (Equiv.sumCongr Equiv.boolEquivPUnitSumPUnit.symm (Equiv.refl _)))).map
      (PortNet.wireBoundaryEquiv _ _).symm

/-- The variable's root end remains joined to the right-hand term's root. -/
theorem variableContextWiring_root (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (closed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed) :
    (c.variableContextWiring x t closed).partner (.inl false) =
      .inr (.inr (.inl (.inl ()))) := by
  have h := (Wiring.respects_map (Equiv.sumCongr (Equiv.refl (Fin c.interface.length))
    (Equiv.sumCongr Equiv.boolEquivPUnitSumPUnit.symm
      (Equiv.refl ((Unit ⊕ t.fragment.Leaf) ⊕ c.GraphForestBoundary))))
        (c.headContextWiring (Term.var x, t) closed)).trans
          (Wiring.respects_map (PortNet.wireBoundaryEquiv _ _).symm _)
  have hr := h (.inr (.inl (.inl ())))
  erw [c.headContextWiring_roots (Term.var x, t) closed] at hr
  exact hr

/-- Cancelling the variable fragment does not itself create a closed wire. -/
theorem variableContextWiring_loops (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (closed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed) :
    let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
    (Wiring.closeWire (c.variableContextWiring x t closed)).2 = 0 := by
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  simp only [Wiring.closeWire, Wiring.loopDelta, variableContextWiring_root,
    Sum.inr_ne_inl, ↓reduceIte]

/-- A variable head equation is its retained forest with the two context ends joined. -/
def variableEquationIso (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (closed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed) :
    let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
    let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
    (({ c with equations := (Term.var x, t) :: c.equations } :
      Config arity).occurrenceNet closed).Iso
        ((t.fragment.net.sum c.graphForest).couple
          (Wiring.closeWire (c.variableContextWiring x t closed)).1) := by
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  let : FinEnum Bool := boolEnum
  let n := t.fragment.net.sum c.graphForest
  let w := c.headContextWiring (Term.var x, t) closed
  have h := (c.headGraphIso (Term.var x, t) closed).trans
    (TermFragment.varSumCoupleIso x n w)
  have hw := Wiring.map_symm_map (PortNet.wireBoundaryEquiv (Fin c.interface.length)
    ((Unit ⊕ t.fragment.Leaf) ⊕ c.GraphForestBoundary)).symm
      (w.map (Equiv.sumCongr (Equiv.refl _)
        (Equiv.sumCongr Equiv.boolEquivPUnitSumPUnit.symm (Equiv.refl _))))
  simp only [Equiv.symm_symm] at hw
  change (c.variableContextWiring x t closed).map (PortNet.wireBoundaryEquiv _ _) = _ at hw
  rw [← hw, PortNet.couple_adjoinWire, variableContextWiring_loops, Nat.add_zero] at h
  exact h

end Geb.InteractionNet.Config

end
