/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.CouplingCancellation
public import Geb.Prototypes.InteractionNet.CouplingComposition
public import Geb.Prototypes.InteractionNet.CouplingIdentity
public import Geb.Prototypes.InteractionNet.WiringRelocation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Closing boundary positions before attaching a context

A boundary matching can join two distinguished positions while extending every other
position to a fresh copy. Composing it with a further context retains that distinguished
wire and attaches the further context directly. The composition itself creates no closed
wires; any closed component created by joining the graph's distinguished positions is
already recorded by their first attachment.

## Main definitions

* {lit}`Wiring.closePairBoundary` — join the distinguished positions and retain all other ends.

## Main statements

* {lit}`PortNet.couple_closePair` — close a boundary pair before attaching the remaining context.

## Tags

interaction net, boundary, assembly, composition, wire, closure
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

private local instance : FinEnum Bool := boolEnum

namespace Wiring

variable {B Γ : Type}

/-- Join two distinguished attachment positions and extend every other boundary position. -/
def closePairBoundary (B : Type) : Wiring (B ⊕ (Bool ⊕ B)) :=
  (wire.sum (identityBoundary B)).map (PortNet.wireBoundaryEquiv B B)

private def closingContextEmbedding : Bool ⊕ (Γ ⊕ B) ↪ (B ⊕ (Bool ⊕ B)) ⊕ (Γ ⊕ B) :=
  Function.Embedding.sumMap (Function.Embedding.inl.trans .inr) (.refl _)

variable [FinEnum B] [FinEnum Γ]

/-- Composing a pair closure with a context keeps its distinguished wire and creates no loops. -/
theorem composeBoundary_closePair (w : Wiring (Γ ⊕ B)) :
    let := boolEnum
    composeBoundary (closePairBoundary B) w =
      ((wire.sum w).map (PortNet.wireBoundaryEquiv Γ B), 0) := by
  let := boolEnum
  dsimp only
  let ports := composeBoundaryPorts (Bool ⊕ B) B Γ
  let v := (closePairBoundary B).sum w
  let r := v.relocation ports (FinEnum.toList B) true
  have free (i j : B) (b : Bool) : v.partner (ports (i, true)) ≠ ports (j, b) := by
    cases b <;> intro h <;> cases h
  have hi : Respects closingContextEmbedding (wire.sum w) v := by
    rintro (b | p)
    · cases b <;> rfl
    · rfl
  have hc := composeBoundary_spec (closePairBoundary B) w
  have hg := glue_relocation ports (FinEnum.toList B) FinEnum.nodup_toList v 0 true
    (fun i _ j _ b ↦ free i j b)
  change glue ports (FinEnum.toList B) (v, 0) = (v.map r, 0) at hg
  dsimp only at hc
  rw [hg] at hc
  have hr := hi.trans (respects_map r v)
  have hw := hr.map_eq hc.1 (PortNet.wireBoundaryEquiv Γ B) (fun p ↦ ?_)
  · exact Prod.ext hw.symm hc.2
  · rcases p with b | (γ | b)
    · change r (.inl (.inr (.inl b))) =
        (Sum.inl (Sum.inr (Sum.inl b)) : (B ⊕ (Bool ⊕ B)) ⊕ (Γ ⊕ B))
      apply relocation_apply_of_outside
      intro i _
      constructor <;> intro h <;> cases h
    · change r (.inr (.inl γ)) = (Sum.inr (Sum.inl γ) : (B ⊕ (Bool ⊕ B)) ⊕ (Γ ⊕ B))
      apply relocation_apply_of_outside
      intro i _
      constructor <;> intro h <;> cases h
    · have he := relocation_apply_cut v ports (FinEnum.toList B) FinEnum.nodup_toList true free b
      rw [ite_eq_left (FinEnum.mem_toList b)] at he
      exact he

end Wiring

namespace PortNet

variable {α C B Γ : Type} {arity : α → ℕ} {label : C → α}
variable [FinEnum C] [FinEnum B] [FinEnum Γ]

/-- Joining a boundary pair can be performed before attaching the remaining matching. -/
theorem couple_closePair (n : PortNet arity label (Bool ⊕ B)) (w : Wiring (Γ ⊕ B)) :
    let := boolEnum
    (n.couple (Wiring.closePairBoundary B)).couple w =
      n.couple ((Wiring.wire.sum w).map (wireBoundaryEquiv Γ B)) := by
  let := boolEnum
  dsimp only
  rw [couple_couple, Wiring.composeBoundary_closePair]
  simp only [Nat.add_zero]

end PortNet

end Geb.InteractionNet

end
