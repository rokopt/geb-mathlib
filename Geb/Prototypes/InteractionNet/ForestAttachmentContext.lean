/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ForestAttachment
public import Geb.Prototypes.InteractionNet.AssemblyEmbedding
public import Geb.Prototypes.InteractionNet.WiringCompose
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Substitution inside a forest's wiring context

The cuts attaching replacement roots are disjoint from the cuts attaching the forest's
external wiring. They can therefore be performed in either order. The common endpoint
space records all original cells, replacement cells and external wires, including closed
components produced by the context.

## Main definitions

* {lit}`TermFragment.AttachmentContextEndpoint` — endpoints before either family of cuts.
* {lit}`TermFragment.attachmentContextPorts` — the external context's attachment cuts.

## Main statements

* {lit}`TermFragment.forestAttach_context_spec` — assemble the context before substitution.

## Tags

interaction net, compiler, forest, substitution, context, gluing
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.TermFragment

open scoped FinEnum

variable {α ν μ I Γ : Type} {arity : α → ℕ} [FinEnum I] [FinEnum Γ]

/-- Roots and replacement leaves exposed by the attached forest. -/
abbrev AttachedForestBoundary (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) :=
  Σ i, Unit ⊕ ((f i).attach (g i)).Leaf

/-- Original and replacement cells with their retained symbols. -/
def attachedForestLabel (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ)
    (c : Σ i, ((f i).attach (g i)).Cell) : α := ((f c.1).attach (g c.1)).label c.2

/-- Context endpoints and every original or replacement fragment endpoint. -/
abbrev AttachmentContextEndpoint (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) (Γ : Type) :=
  (Γ ⊕ AttachedForestBoundary f g) ⊕ ForestAttachmentEndpoint f g

/-- Structural endpoint equality for the context and the allocated fragments. -/
@[instance_reducible] def attachmentContextDecidableEq (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) :
    DecidableEq (AttachmentContextEndpoint f g Γ) :=
  let : DecidableEq (ForestAttachmentEndpoint f g) := forestAttachmentDecidableEq f g
  let _ (i : I) : DecidableEq ((f i).attach (g i)).Leaf :=
    ((f i).attach (g i)).leafEnum.decEq
  inferInstance

/-- Embed coupling's allocated endpoints before the forest's own substitutions are performed. -/
def attachedForestContextEmbedding (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) :
    PortNet.CouplingEndpoint arity (attachedForestLabel f g) Γ (AttachedForestBoundary f g) ↪
      AttachmentContextEndpoint f g Γ :=
  Function.Embedding.sumMap (.refl _) (forestAttachmentEmbedding f g)

/-- Attach every exposed root or replacement leaf to the surrounding matching. -/
def attachmentContextPorts (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) (Γ : Type) :
    AttachedForestBoundary f g × Bool ↪ AttachmentContextEndpoint f g Γ :=
  (PortNet.couplePorts arity (attachedForestLabel f g) Γ
    (AttachedForestBoundary f g)).trans (attachedForestContextEmbedding f g)

/-- Locate the final external boundary and all retained cells in the common allocation. -/
def attachmentContextEmbedding (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) (Γ : Type) :
    Endpoint arity (attachedForestLabel f g) Γ ↪ AttachmentContextEndpoint f g Γ :=
  (PortNet.coupleEmbedding arity (attachedForestLabel f g) Γ
    (AttachedForestBoundary f g)).trans (attachedForestContextEmbedding f g)

/-- Allocate the surrounding matching alongside the complete substitution forest. -/
def attachmentContextState (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ)
    (w : Wiring (Γ ⊕ AttachedForestBoundary f g)) :
    Wiring (AttachmentContextEndpoint f g Γ) × ℕ :=
  (w.sum (forestAttachmentState f g).1, (forestAttachmentState f g).2)

private theorem attachmentFirst_spec (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ)
    (w : Wiring (Γ ⊕ AttachedForestBoundary f g)) :
    let := sigmaEnum (C := fun i ↦ ((f i).attach (g i)).Cell)
    let := sigmaEnum (C := fun i ↦ Unit ⊕ ((f i).attach (g i)).Leaf)
    let : DecidableEq (AttachmentContextEndpoint f g Γ) := attachmentContextDecidableEq f g
    let n := PortNet.sigma (fun i ↦ ((f i).attach (g i)).net)
    let s := Wiring.glue (attachmentContextPorts f g Γ) (FinEnum.toList _)
      (Wiring.glue ((forestAttachmentPorts f g).trans .inr)
        (forestOrder (FinEnum.toList I) f) (attachmentContextState f g w))
    Wiring.Respects (attachmentContextEmbedding f g Γ) (n.couple w).wiring s.1 ∧
      (n.couple w).loops = s.2 := by
  let := sigmaEnum (C := fun i ↦ ((f i).attach (g i)).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ ((f i).attach (g i)).Leaf)
  let : DecidableEq (AttachmentContextEndpoint f g Γ) := attachmentContextDecidableEq f g
  dsimp only
  let n := PortNet.sigma (fun i ↦ ((f i).attach (g i)).net)
  let s := Wiring.glue ((forestAttachmentPorts f g).trans .inr)
    (forestOrder (FinEnum.toList I) f) (attachmentContextState f g w)
  have hi := forestAttach_in f g (.inr) (attachmentContextState f g w)
    (Wiring.respects_inr w (forestAttachmentState f g).1) 0 (Nat.add_zero _)
  have he : Wiring.Respects (attachedForestContextEmbedding f g) (w.sum n.wiring) s.1 := by
    rintro (p | p)
    · apply Wiring.glue_keeps
      · intro i b h; cases h
      · intro i b h; cases h
      · rfl
    · exact hi.1 p
  have h := n.couple_in w (attachedForestContextEmbedding f g) s he 0 hi.2
  exact ⟨h.1, (Nat.add_zero _).symm.trans h.2⟩

omit [FinEnum I] [FinEnum Γ] in
private theorem context_disjoint (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ)
    (p : AttachedForestBoundary f g) (b : Bool) (q : Σ i, (f i).Leaf) (c : Bool) :
    attachmentContextPorts f g Γ (p, b) ≠
      Sum.inr (forestAttachmentPorts f g (q, c)) := by
  cases b with
  | false => intro h; cases h
  | true =>
    intro h
    exact forestAttachmentEmbedding_ne f g (.inl p) q c (Sum.inr.inj h)

/-- Assemble the forest's context before attaching replacements, with identical wires and loops. -/
theorem forestAttach_context_spec (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ)
    (w : Wiring (Γ ⊕ AttachedForestBoundary f g)) :
    let := sigmaEnum (C := fun i ↦ ((f i).attach (g i)).Cell)
    let := sigmaEnum (C := fun i ↦ Unit ⊕ ((f i).attach (g i)).Leaf)
    let : DecidableEq (AttachmentContextEndpoint f g Γ) := attachmentContextDecidableEq f g
    let n := PortNet.sigma (fun i ↦ ((f i).attach (g i)).net)
    let s := Wiring.glue ((forestAttachmentPorts f g).trans .inr)
      (forestOrder (FinEnum.toList I) f)
      (Wiring.glue (attachmentContextPorts f g Γ) (FinEnum.toList _)
        (attachmentContextState f g w))
    Wiring.Respects (attachmentContextEmbedding f g Γ) (n.couple w).wiring s.1 ∧
      (n.couple w).loops = s.2 := by
  let := sigmaEnum (C := fun i ↦ ((f i).attach (g i)).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ ((f i).attach (g i)).Leaf)
  let : DecidableEq (AttachmentContextEndpoint f g Γ) := attachmentContextDecidableEq f g
  dsimp only
  have h := attachmentFirst_spec f g w
  have hc := Wiring.glue_glue (attachmentContextPorts f g Γ)
    ((forestAttachmentPorts f g).trans .inr) (context_disjoint f g) (FinEnum.toList _)
    (forestOrder (FinEnum.toList I) f) (attachmentContextState f g w)
  rw [hc]
  exact h

end Geb.InteractionNet.TermFragment

end
