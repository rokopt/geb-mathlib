/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.BoundarySplice
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Isolating a paired boundary wire

When an attachment context already joins two distinguished boundary positions, that wire
can be separated from the remaining matching. Attaching the context then amounts to
closing those positions in the graph and attaching the remaining matching. A component
closed by this operation is counted only in the graph's boundary closure.

## Main statements

* {lit}`Wiring.closeWire_decompose` — separate a distinguished existing wire.
* {lit}`PortNet.couple_pairedBoundary` — close its graph endpoints before attaching the rest.

## Tags

interaction net, boundary, matching, wire, closure, assembly
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

/-- An existing distinguished wire is disjoint from the matching on all other positions. -/
theorem Wiring.closeWire_decompose {P : Type} [DecidableEq P] (w : Wiring (Bool ⊕ P))
    (h : w.partner (.inl false) = .inl true) :
    Wiring.wire.sum w.closeWire.1 = w := by
  have hs := w.closeWire_respects
  rw [w.force_of_partner_eq h] at hs
  ext p
  rcases p with b | p
  · cases b
    · exact h.symm
    · exact w.partner_eq_iff.mp h
  · exact (hs p).symm

namespace PortNet

variable {α C B Γ : Type} {arity : α → ℕ} {label : C → α}
variable [FinEnum C] [FinEnum B] [FinEnum Γ]

/-- A paired context boundary can be closed in the graph before attaching the other wires. -/
theorem couple_pairedBoundary (n : PortNet arity label (Bool ⊕ B))
    (w : Wiring (Γ ⊕ (Bool ⊕ B)))
    (h : w.partner (.inr (.inl false)) = .inr (.inl true)) :
    let := boolEnum
    n.couple w = n.closeBoundaryPair.couple
      (Wiring.closeWire (w.map (wireBoundaryEquiv Γ B).symm)).1 := by
  let := boolEnum
  dsimp only
  rw [← couple_closePair_eq, couple_closePair]
  have hm : (w.map (wireBoundaryEquiv Γ B).symm).partner (.inl false) = .inl true := by
    exact congrArg (wireBoundaryEquiv Γ B).symm h
  rw [Wiring.closeWire_decompose _ hm]
  exact congrArg n.couple (Wiring.map_symm_map (wireBoundaryEquiv Γ B).symm w).symm

end PortNet

end Geb.InteractionNet

end
