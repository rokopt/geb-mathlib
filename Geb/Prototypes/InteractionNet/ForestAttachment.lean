/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermAttachmentAgent
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Attaching replacements throughout a forest

Attaching replacements separately inside each term agrees with gluing their leaf-to-root
wires in one disjoint forest. The comparison retains every cell, named leaf and closed wire.
It supplies a common endpoint space for comparing substitution with configuration assembly.

## Main definitions

* {lit}`TermFragment.forestAttachmentPorts` — all leaf-to-root cuts in a forest.
* {lit}`TermFragment.forestAttachmentEmbedding` — the attached forest's surviving endpoints.

## Main statements

* {lit}`TermFragment.forestAttach_spec` — component attachments agree with the global cuts.

## Tags

interaction net, compiler, forest, substitution, attachment, gluing
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.TermFragment

open scoped FinEnum

variable {α ν μ I : Type} {arity : α → ℕ} [FinEnum I]

/-- All original and replacement endpoints, indexed by the original forest root. -/
abbrev ForestAttachmentEndpoint (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) := Σ i, AttachmentEndpoint (f i) (g i)

/-- Structural endpoint equality uses each fragment's explicit finite indices. -/
@[instance_reducible] def forestAttachmentDecidableEq (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) :
    DecidableEq (ForestAttachmentEndpoint f g) :=
  let _ (i : I) : DecidableEq (AttachmentEndpoint (f i) (g i)) :=
    attachmentDecidableEq (f i) (g i)
  inferInstance

/-- Pair each original leaf with its replacement root in the same forest component. -/
def forestAttachmentPorts (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) :
    (Σ i, (f i).Leaf) × Bool ↪ ForestAttachmentEndpoint f g where
  toFun p := ⟨p.1.1, attachmentPorts (f p.1.1) (g p.1.1) (p.1.2, p.2)⟩
  inj' := by
    rintro ⟨⟨i, p⟩, b⟩ ⟨⟨j, q⟩, c⟩ h
    have hij : i = j := congrArg Sigma.fst h
    subst j
    have hp := (attachmentPorts (f i) (g i)).injective
      (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    cases hp
    rfl

/-- Locate the disjoint attached forest inside the original and replacement endpoint family. -/
def forestAttachmentEmbedding (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) :
    Endpoint arity (fun c : Σ i, ((f i).attach (g i)).Cell ↦
      ((f c.1).attach (g c.1)).label c.2)
      (Σ i, Unit ⊕ ((f i).attach (g i)).Leaf) ↪ ForestAttachmentEndpoint f g :=
  (PortNet.sigmaEndpointEquiv arity
    (fun i ↦ ((f i).attach (g i)).label)).symm.toEmbedding.trans
      (Function.Embedding.sigmaMap (.refl I) (fun i ↦ attachmentEmbedding (f i) (g i)))

omit [FinEnum I] in
/-- Surviving forest endpoints avoid every original leaf-to-root cut. -/
theorem forestAttachmentEmbedding_ne (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ)
    (p : Endpoint arity (fun c : Σ i, ((f i).attach (g i)).Cell ↦
      ((f c.1).attach (g c.1)).label c.2) (Σ i, Unit ⊕ ((f i).attach (g i)).Leaf))
    (q : Σ i, (f i).Leaf) (b : Bool) :
    forestAttachmentEmbedding f g p ≠ forestAttachmentPorts f g (q, b) := by
  let r := (PortNet.sigmaEndpointEquiv arity
    (fun i ↦ ((f i).attach (g i)).label)).symm p
  change (Sigma.mk r.1 (attachmentEmbedding (f r.1) (g r.1) r.2) :
    ForestAttachmentEndpoint f g) ≠
      Sigma.mk q.1 (attachmentPorts (f q.1) (g q.1) (q.2, b))
  intro h
  rcases q with ⟨j, q⟩
  have hij : r.1 = j := congrArg Sigma.fst h
  subst j
  exact ((attachmentEndpointEquiv (f r.1) (g r.1)).symm r.2).property q b
    (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

/-- Allocate every component's original and replacement matchings and closed wires. -/
def forestAttachmentState (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) :
    Wiring (ForestAttachmentEndpoint f g) × ℕ :=
  (Wiring.sigma (fun i ↦ (attachmentState (f i) (g i)).1),
    ((FinEnum.toList I).map fun i ↦ (attachmentState (f i) (g i)).2).sum)

/-- Each component follows precisely its own leaf-to-root cuts in the forest schedule. -/
theorem forestAttachment_component (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) (i : I) :
    let : DecidableEq (AttachmentEndpoint (f i) (g i)) := attachmentDecidableEq (f i) (g i)
    let : DecidableEq (ForestAttachmentEndpoint f g) := forestAttachmentDecidableEq f g
    Wiring.Respects (.sigmaMk i)
      (Wiring.glue (attachmentPorts (f i) (g i)) (f i).order
        (attachmentState (f i) (g i))).1
      (Wiring.glue (forestAttachmentPorts f g) (forestOrder (FinEnum.toList I) f)
        (forestAttachmentState f g)).1 := by
  dsimp only
  let : DecidableEq (AttachmentEndpoint (f i) (g i)) := attachmentDecidableEq (f i) (g i)
  let : DecidableEq (ForestAttachmentEndpoint f g) := forestAttachmentDecidableEq f g
  have start : Wiring.Respects (.sigmaMk i) (attachmentState (f i) (g i)).1
      (forestAttachmentState f g).1 := fun _ ↦ rfl
  have inside : ∀ j p, selectFiber i j = some p → ∀ b,
      forestAttachmentPorts f g (j, b) =
        Function.Embedding.sigmaMk i (attachmentPorts (f i) (g i) (p, b)) := by
    intro j p hj b
    rw [selectFiber_some hj]
    rfl
  have outside : ∀ j, selectFiber i j = none → ∀ p b,
      Function.Embedding.sigmaMk i p ≠ forestAttachmentPorts f g (j, b) := by
    intro j hj p b he
    exact selectFiber_none hj (congrArg Sigma.fst he).symm
  have h := start.glue_select (attachmentPorts (f i) (g i)) (forestAttachmentPorts f g)
    (selectFiber i) inside outside (forestOrder (FinEnum.toList I) f)
    (attachmentState (f i) (g i)) (forestAttachmentState f g)
  have ho := selectFiber_forestOrder (FinEnum.toList I) FinEnum.nodup_toList f i
  simp only [FinEnum.mem_toList, ↓reduceIte] at ho
  rw [ho] at h
  exact h

/-- Attaching replacements componentwise agrees with the global forest's cuts and loop count. -/
theorem forestAttach_spec (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) :
    let : DecidableEq (ForestAttachmentEndpoint f g) := forestAttachmentDecidableEq f g
    let w := Wiring.glue (forestAttachmentPorts f g) (forestOrder (FinEnum.toList I) f)
      (forestAttachmentState f g)
    Wiring.Respects (forestAttachmentEmbedding f g)
      (PortNet.sigma (fun i ↦ ((f i).attach (g i)).net)).wiring w.1 ∧
      (PortNet.sigma (fun i ↦ ((f i).attach (g i)).net)).loops = w.2 := by
  dsimp only
  let : DecidableEq (ForestAttachmentEndpoint f g) := forestAttachmentDecidableEq f g
  constructor
  · have h : Wiring.Respects
        (Function.Embedding.sigmaMap (.refl I) (fun i ↦ attachmentEmbedding (f i) (g i)))
        (Wiring.sigma (fun i ↦ ((f i).attach (g i)).net.wiring))
        (Wiring.glue (forestAttachmentPorts f g) (forestOrder (FinEnum.toList I) f)
          (forestAttachmentState f g)).1 := by
      rintro ⟨i, p⟩
      exact (((f i).attach_spec (g i)).1.trans (forestAttachment_component f g i)) p
    exact (Wiring.respects_map_symm (PortNet.sigmaEndpointEquiv arity
      (fun i ↦ ((f i).attach (g i)).label)) _).trans h
  · have h := Wiring.glue_loops_of_free_right (forestAttachmentPorts f g)
      (forestOrder (FinEnum.toList I) f)
      (forestOrder_unique _ FinEnum.nodup_toList f) (forestAttachmentState f g) ?_
    · rw [h]
      change ((FinEnum.toList I).map fun i ↦ ((f i).attach (g i)).net.loops).sum = _
      simp only [attach_loops, forestAttachmentState, attachmentState]
    · rintro ⟨i, p⟩ _ ⟨j, q⟩ _ b he
      have hij : i = j := congrArg Sigma.fst he
      subst j
      have he := eq_of_heq (Sigma.mk.inj_iff.mp he).2
      cases b with
      | false => cases he
      | true =>
        have hpq : p = q := congrArg Sigma.fst (Sum.inr.inj he)
        subst q
        exact (g i p).net.wiring.fixedPointFree (.inl (.inl ()))
          (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj he)).2)

/-- Forest attachment can be performed inside any larger matching, retaining its loop offset. -/
theorem forestAttach_in {P : Type} [DecidableEq P] (f : I → TermFragment arity ν)
    (g : ∀ i, (f i).Leaf → TermFragment arity μ) (e : ForestAttachmentEndpoint f g ↪ P)
    (ambient : Wiring P × ℕ) (he : Wiring.Respects e (forestAttachmentState f g).1 ambient.1)
    (extra : ℕ) (hl : (forestAttachmentState f g).2 + extra = ambient.2) :
    let w := Wiring.glue ((forestAttachmentPorts f g).trans e)
      (forestOrder (FinEnum.toList I) f) ambient
    Wiring.Respects ((forestAttachmentEmbedding f g).trans e)
      (PortNet.sigma (fun i ↦ ((f i).attach (g i)).net)).wiring w.1 ∧
      (PortNet.sigma (fun i ↦ ((f i).attach (g i)).net)).loops + extra = w.2 := by
  let : DecidableEq (ForestAttachmentEndpoint f g) := forestAttachmentDecidableEq f g
  have hs := forestAttach_spec f g
  have hg := he.glue_offset (forestAttachmentPorts f g) (forestOrder (FinEnum.toList I) f)
    (forestAttachmentState f g) ambient extra hl
  exact ⟨hs.1.trans hg.1, (congrArg (· + extra) hs.2).trans hg.2⟩

end Geb.InteractionNet.TermFragment

end
