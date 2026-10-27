/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermGraphSubstitution
public import Geb.Prototypes.InteractionNet.TermGraphAttachment
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Cancellation of a variable fragment

A variable fragment is a single wire. Attaching a replacement to its named end leaves
exactly the replacement graph, with the original root taking the place of the replacement
root. The explicit endpoint bijection preserves the matching and every closed wire.
This is the variable case of graph substitution.

## Main statements

* {lit}`TermFragment.attach_var_wiring` — variable attachment preserves the replacement wires.
* {lit}`TermFragment.attach_var_loops` — variable attachment preserves its closed wires.

## Tags

interaction net, compiler, variable, substitution, cancellation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.TermFragment

open scoped FinEnum

variable {α ν μ : Type} {arity : α → ℕ}

/-- Identify a variable's wire and its sole replacement with the general subdivision space. -/
def variableAttachmentAmbient (x : ν) (g : TermFragment arity μ) :
    Bool ⊕ Endpoint arity g.label (Unit ⊕ g.Leaf) ≃
      AttachmentEndpoint (var x) (fun _ ↦ g) where
  toFun p := match p with
    | .inl false => .inl (.inl (.inl ()))
    | .inl true => .inl (.inl (.inr ()))
    | .inr p => .inr ⟨(), p⟩
  invFun p := match p with
    | .inl (.inl (.inl _)) => .inl false
    | .inl (.inl (.inr _)) => .inl true
    | .inl (.inr ⟨c, _⟩) => Fin.elim0 c
    | .inr ⟨_, p⟩ => .inr p
  left_inv p := by rcases p with b | p; cases b <;> rfl; rfl
  right_inv p := by
    rcases p with ((u | v) | ⟨c, p⟩) | ⟨u, p⟩
    · rfl
    · rfl
    · exact Fin.elim0 c
    · rfl

/-- The subdivision presentation has exactly the variable and replacement's allocated wires. -/
theorem variableAttachmentAmbient_wiring (x : ν) (g : TermFragment arity μ) :
    (Wiring.wire.sum g.net.wiring).map (variableAttachmentAmbient x g) =
      (var (arity := arity) x).net.wiring.sum (Wiring.sigma fun _ : Unit ↦ g.net.wiring) := by
  apply Wiring.ext
  funext p
  rcases p with ((u | v) | ⟨c, p⟩) | ⟨u, p⟩
  · rfl
  · rfl
  · exact Fin.elim0 c
  · rfl

/-- Reindex a replacement's root, leaves and cells as the result of variable attachment. -/
def variableAttachmentEndpoints (x : ν) (g : TermFragment arity μ) :
    Endpoint arity g.label (Unit ⊕ g.Leaf) ≃
      Endpoint arity (attachmentLabel (var x) (fun _ ↦ g))
        (Unit ⊕ (Σ _ : Unit, g.Leaf)) :=
  endpointEquiv arity (Equiv.sumCongr (Equiv.refl Unit) (variableLeaves g.Leaf))
    (variableCells g.Cell) (fun _ ↦ rfl)

/-- Attaching to a variable preserves the replacement wires under explicit indexing. -/
theorem attach_var_wiring (x : ν) (g : TermFragment arity μ) :
    g.net.wiring.map (variableAttachmentEndpoints x g) =
      ((var x).attach (fun _ ↦ g)).net.wiring := by
  let : DecidableEq (Endpoint arity g.label (Unit ⊕ g.Leaf)) := g.endpointDecidableEq
  let : DecidableEq (AttachmentEndpoint (var x) (fun _ ↦ g)) :=
    attachmentDecidableEq (var x) (fun _ ↦ g)
  have h := (Wiring.shiftEndpoint_respects g.net.wiring (.inl (.inl ()))).trans
    (Wiring.respects_map (variableAttachmentAmbient x g) _)
  rw [Wiring.force_map _ _ (by intro he; cases he), variableAttachmentAmbient_wiring] at h
  have ha := ((var (arity := arity) x).attach_spec (fun _ ↦ g)).1
  apply h.map_eq ha (variableAttachmentEndpoints x g)
  intro p
  rcases p with (u | p) | ⟨c, p⟩
  · rfl
  · rfl
  · rfl

/-- Attaching a replacement to a variable preserves its closed-wire count. -/
theorem attach_var_loops (x : ν) (g : TermFragment arity μ) :
    ((var x).attach (fun _ ↦ g)).net.loops = g.net.loops := by
  rw [attach_loops]
  simp only [var, PortNet.identity, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.zero_add]

end Geb.InteractionNet.TermFragment

end
