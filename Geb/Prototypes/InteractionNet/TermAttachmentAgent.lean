/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermGraphAttachment
public import Geb.Prototypes.InteractionNet.WiringSelection
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Locality of attachment beneath an agent

An agent's child fragments occupy disjoint endpoint regions. Selecting one child's leaf
occurrences from the full attachment order recovers that child's own order. Its allocated
matching embeds in the parent's allocation, and its gluing execution remains embedded
through the parent's full schedule.

## Main definitions

* {lit}`TermFragment.selectFiber` — select occurrences belonging to one indexed child.
* {lit}`TermFragment.childAttachmentEmbedding` — embed one child's attachment endpoints.

## Main statements

* {lit}`TermFragment.childAttachment_start` — the embedding preserves the allocated matching.
* {lit}`TermFragment.childAttachment_glue` — attachment preserves the child embedding.

## Tags

interaction net, compiler, substitution, agent, child, locality
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.TermFragment

open scoped FinEnum

variable {I : Type} {L : I → Type} [DecidableEq I]

/-- Keep precisely the occurrences whose outer index is the selected child. -/
def selectFiber (i : I) (p : Σ j, L j) : Option (L i) :=
  if h : p.1 = i then some (h ▸ p.2) else none

/-- Selecting an occurrence in its own fiber retains it. -/
theorem selectFiber_self (i : I) (p : L i) : selectFiber i ⟨i, p⟩ = some p := by
  simp only [selectFiber, ↓reduceDIte]

/-- Selecting an occurrence from a different fiber discards it. -/
theorem selectFiber_ne {i j : I} (h : j ≠ i) (p : L j) : selectFiber i ⟨j, p⟩ = none := by
  simp only [selectFiber, h, ↓reduceDIte]

/-- A successful selection identifies the original occurrence exactly. -/
theorem selectFiber_some {i : I} {p : Σ j, L j} {q : L i}
    (h : selectFiber i p = some q) : p = ⟨i, q⟩ := by
  rcases p with ⟨j, p⟩
  unfold selectFiber at h
  split at h
  · rename_i hj
    change j = i at hj
    subst j
    exact congrArg (Sigma.mk i) (Option.some.inj h)
  · cases h

/-- A discarded occurrence belongs to a different fiber. -/
theorem selectFiber_none {i : I} {p : Σ j, L j}
    (h : selectFiber i p = none) : p.1 ≠ i := by
  intro he
  rcases p with ⟨j, p⟩
  change j = i at he
  subst j
  rw [selectFiber_self] at h
  cases h

private theorem selectFiber_map_self (i : I) (ps : List (L i)) :
    (ps.map (Sigma.mk i)).filterMap (selectFiber i) = ps := by
  refine List.rec (motive := fun ps : List (L i) ↦
    (ps.map (Sigma.mk i)).filterMap (selectFiber i) = ps) rfl (fun p ps ih ↦ ?_) ps
  simp only [List.map_cons, List.filterMap_cons, selectFiber_self, ih]

private theorem selectFiber_map_ne {i j : I} (h : j ≠ i) (ps : List (L j)) :
    (ps.map (Sigma.mk j)).filterMap (selectFiber i) = [] := by
  refine List.rec (motive := fun ps : List (L j) ↦
    (ps.map (Sigma.mk j)).filterMap (selectFiber i) = []) rfl (fun p ps ih ↦ ?_) ps
  simp only [List.map_cons, List.filterMap_cons, selectFiber_ne h, ih]

/-- Selecting a fiber from a duplicate-free forest order recovers exactly its own leaf order. -/
theorem selectFiber_forestOrder {α ν : Type} {arity : α → ℕ}
    (order : List I) (unique : order.Nodup) (f : I → TermFragment arity ν) (i : I) :
    (forestOrder order f).filterMap (selectFiber i) = if i ∈ order then (f i).order else [] := by
  revert unique
  refine List.rec (fun _ ↦ rfl) (fun j order ih unique ↦ ?_) order
  have hn := List.nodup_cons.mp unique
  change (((f j).order.map (Sigma.mk j)) ++ forestOrder order f).filterMap (selectFiber i) = _
  rw [List.filterMap_append]
  by_cases hj : j = i
  · subst j
    rw [selectFiber_map_self, ih hn.2]
    simp only [List.mem_cons_self, hn.1, ↓reduceIte, List.append_nil]
  · rw [selectFiber_map_ne hj, List.nil_append, ih hn.2]
    simp only [List.mem_cons, Ne.symm hj, false_or]

variable {α ν μ : Type} {arity : α → ℕ}

/-- A child's original and replacement endpoints occupy a disjoint part of the allocation. -/
def childAttachmentEmbedding (a : α) (f : Fin (arity a) → TermFragment arity ν)
    (g : (Σ i, (f i).Leaf) → TermFragment arity μ) (i : Fin (arity a)) :
    AttachmentEndpoint (f i) (fun p ↦ g ⟨i, p⟩) ↪ AttachmentEndpoint (agent a f) g :=
  (((Function.Embedding.sigmaMk i).trans .inr).trans
      (agentEndpointEquiv a f).toEmbedding).sumMap
    ((Function.Embedding.sigmaMk i).trans
      (Equiv.sigmaAssoc (fun i p ↦ Endpoint arity (g ⟨i, p⟩).label
        (Unit ⊕ (g ⟨i, p⟩).Leaf))).symm.toEmbedding)

/-- The child's endpoint inclusion preserves the original disjoint matchings. -/
theorem childAttachment_start (a : α) (f : Fin (arity a) → TermFragment arity ν)
    (g : (Σ i, (f i).Leaf) → TermFragment arity μ) (i : Fin (arity a)) :
    Wiring.Respects (childAttachmentEmbedding a f g i)
      (attachmentState (f i) (fun p ↦ g ⟨i, p⟩)).1 (attachmentState (agent a f) g).1 := by
  intro p
  cases p with
  | inl p =>
    change Sum.inl (((agent a f).net.wiring).partner
      (agentEndpointEquiv a f (.inr ⟨i, p⟩))) =
        Sum.inl (agentEndpointEquiv a f (.inr ⟨i, (f i).net.wiring.partner p⟩))
    exact congrArg Sum.inl (Wiring.map_partner (agentEndpointEquiv a f) _ (.inr ⟨i, p⟩))
  | inr p => rfl

/-- The child attachment embedding transports each of its own leaf-to-root cuts. -/
theorem childAttachment_ports (a : α) (f : Fin (arity a) → TermFragment arity ν)
    (g : (Σ i, (f i).Leaf) → TermFragment arity μ) (i : Fin (arity a))
    (p : (f i).Leaf) (b : Bool) :
    childAttachmentEmbedding a f g i (attachmentPorts (f i) (fun p ↦ g ⟨i, p⟩) (p, b)) =
      attachmentPorts (agent a f) g (⟨i, p⟩, b) := by
  cases b <;> rfl

/-- Cuts at another child have no endpoint in this child's allocated matching. -/
theorem childAttachment_outside (a : α) (f : Fin (arity a) → TermFragment arity ν)
    (g : (Σ i, (f i).Leaf) → TermFragment arity μ) {i j : Fin (arity a)} (hji : j ≠ i)
    (p : AttachmentEndpoint (f i) (fun p ↦ g ⟨i, p⟩)) (q : (f j).Leaf) (b : Bool) :
    childAttachmentEmbedding a f g i p ≠ attachmentPorts (agent a f) g (⟨j, q⟩, b) := by
  cases p with
  | inl p =>
    cases b with
    | false =>
      intro h
      have he : agentEndpointEquiv a f (.inr ⟨i, p⟩) =
          agentEndpointEquiv a f (.inr ⟨j, .inl (.inr q)⟩) := Sum.inl.inj h
      exact hji (congrArg Sigma.fst (Sum.inr.inj ((agentEndpointEquiv a f).injective he))).symm
    | true => intro h; cases h
  | inr p =>
    cases b with
    | false => intro h; cases h
    | true =>
      intro h
      exact hji (congrArg (fun p ↦ p.1.1) (Sum.inr.inj h)).symm

/-- The child's completed gluing embeds in the parent's complete attachment execution. -/
theorem childAttachment_glue (a : α) (f : Fin (arity a) → TermFragment arity ν)
    (g : (Σ i, (f i).Leaf) → TermFragment arity μ) (i : Fin (arity a)) :
    let : DecidableEq (AttachmentEndpoint (f i) (fun p ↦ g ⟨i, p⟩)) :=
      attachmentDecidableEq (f i) (fun p ↦ g ⟨i, p⟩)
    let : DecidableEq (AttachmentEndpoint (agent a f) g) :=
      attachmentDecidableEq (agent a f) g
    Wiring.Respects (childAttachmentEmbedding a f g i)
      (Wiring.glue (attachmentPorts (f i) (fun p ↦ g ⟨i, p⟩)) (f i).order
        (attachmentState (f i) (fun p ↦ g ⟨i, p⟩))).1
      (Wiring.glue (attachmentPorts (agent a f) g) (agent a f).order
        (attachmentState (agent a f) g)).1 := by
  dsimp only
  let : DecidableEq (AttachmentEndpoint (f i) (fun p ↦ g ⟨i, p⟩)) :=
    attachmentDecidableEq (f i) (fun p ↦ g ⟨i, p⟩)
  let : DecidableEq (AttachmentEndpoint (agent a f) g) :=
    attachmentDecidableEq (agent a f) g
  have hi : ∀ j p, selectFiber i j = some p → ∀ b,
      attachmentPorts (agent a f) g (j, b) =
        childAttachmentEmbedding a f g i
          (attachmentPorts (f i) (fun p ↦ g ⟨i, p⟩) (p, b)) := by
    intro j p hj b
    rw [selectFiber_some hj]
    exact (childAttachment_ports a f g i p b).symm
  have ho' : ∀ j, selectFiber i j = none → ∀ p b,
      childAttachmentEmbedding a f g i p ≠ attachmentPorts (agent a f) g (j, b) := by
    intro j hj p b
    exact childAttachment_outside a f g (selectFiber_none hj) p j.2 b
  have h := (childAttachment_start a f g i).glue_select
    (attachmentPorts (f i) (fun p ↦ g ⟨i, p⟩)) (attachmentPorts (agent a f) g)
    (selectFiber i) hi ho'
    (agent a f).order (attachmentState (f i) (fun p ↦ g ⟨i, p⟩))
    (attachmentState (agent a f) g)
  have ho := @selectFiber_forestOrder (Fin (arity a)) (instDecidableEqFin _) α ν arity
    (List.finRange (arity a)) (List.nodup_finRange _) f i
  simp only [List.mem_finRange, ↓reduceIte] at ho
  change ((agent a f).order.filterMap (selectFiber i)) = (f i).order at ho
  dsimp only [agent, agentOrder] at h ho
  rw [ho] at h
  exact h

end Geb.InteractionNet.TermFragment

end
