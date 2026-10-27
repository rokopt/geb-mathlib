/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermAttachmentAgent
public import Geb.Prototypes.InteractionNet.TermAttachmentVariable
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Term substitution as graph attachment

Textual substitution and graph attachment retain the same original cells and insert the
same occurrence-indexed replacement cells. The occurrence bijections identify their
surviving endpoints. Child attachment embeddings express this correspondence beneath an
agent without imposing an order on independent wire splices.

## Main definitions

* {lit}`Term.substitutionEndpoints` — identify the endpoints after textual and graph substitution.
* {lit}`Term.substitutionEmbedding` — locate substituted syntax in the allocated graph.

## Main statements

* {lit}`Term.fragment_subst_wiring` — textual substitution agrees with graph attachment.
* {lit}`Term.fragment_subst_loops` — the correspondence preserves closed-wire counts.

## Tags

interaction net, compiler, substitution, graph, simulation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Term

open scoped FinEnum
open TermFragment

variable {α ν μ : Type} {arity : α → ℕ}

/-- A replacement fragment is allocated separately at every occurrence of its name. -/
def substitutionFragments (σ : ν → Term arity μ) (t : Term arity ν) :
    t.fragment.Leaf → TermFragment arity μ := fun p ↦ (σ (t.fragment.name p)).fragment

/-- Identify surviving endpoints by their original or replacement occurrence positions. -/
def substitutionEndpoints (σ : ν → Term arity μ) (t : Term arity ν) :
    Endpoint arity (t.subst σ).fragment.label (Unit ⊕ (t.subst σ).fragment.Leaf) ≃
      Endpoint arity (attachmentLabel t.fragment (substitutionFragments σ t))
        (Unit ⊕ (Σ p, (substitutionFragments σ t p).Leaf)) :=
  endpointEquiv arity (Equiv.sumCongr (Equiv.refl Unit) (substLeafEquiv σ t))
    (substCellEquiv σ t) (substCellEquiv_label σ t)

/-- Locate the substituted term's endpoints in the original and allocated replacement graphs. -/
def substitutionEmbedding (σ : ν → Term arity μ) (t : Term arity ν) :
    Endpoint arity (t.subst σ).fragment.label (Unit ⊕ (t.subst σ).fragment.Leaf) ↪
      AttachmentEndpoint t.fragment (substitutionFragments σ t) :=
  (substitutionEndpoints σ t).toEmbedding.trans
    (attachmentEmbedding t.fragment (substitutionFragments σ t))

/-- An original cell identified by substitution retains its symbol. -/
theorem substitution_retained_label (σ : ν → Term arity μ) (t : Term arity ν)
    (c : (t.subst σ).fragment.Cell) (d : t.fragment.Cell)
    (h : substCellEquiv σ t c = .inl d) :
    t.fragment.label d = (t.subst σ).fragment.label c := by
  simpa only [h, Sum.elim_inl] using substCellEquiv_label σ t c

/-- An inserted cell identified by substitution retains its replacement symbol. -/
theorem substitution_inserted_label (σ : ν → Term arity μ) (t : Term arity ν)
    (c : (t.subst σ).fragment.Cell)
    (d : Σ p : t.fragment.Leaf, (substitutionFragments σ t p).Cell)
    (h : substCellEquiv σ t c = .inr d) :
    (substitutionFragments σ t d.1).label d.2 = (t.subst σ).fragment.label c := by
  exact (congrArg (attachmentLabel t.fragment (substitutionFragments σ t)) h).symm.trans
    (substCellEquiv_label σ t c)

/-- A retained cell port lies in the original fragment's endpoint region. -/
theorem substitutionEmbedding_retained (σ : ν → Term arity μ) (t : Term arity ν)
    (c : (t.subst σ).fragment.Cell) (d : t.fragment.Cell)
    (h : substCellEquiv σ t c = .inl d)
    (p : Fin (arity ((t.subst σ).fragment.label c) + 1)) :
    substitutionEmbedding σ t (.inr ⟨c, p⟩) =
      .inl (.inr ⟨d, Fin.cast (congrArg (fun a ↦ arity a + 1)
        (substitution_retained_label σ t c d h).symm) p⟩) := by
  have he : substitutionEndpoints σ t (.inr ⟨c, p⟩) =
      .inr ⟨.inl d, Fin.cast (congrArg (fun a ↦ arity a + 1)
        (substitution_retained_label σ t c d h).symm) p⟩ := by
    apply congrArg Sum.inr
    apply Sigma.ext h
    apply (Fin.heq_ext_iff (congrArg
      (fun c ↦ arity (attachmentLabel t.fragment (substitutionFragments σ t) c) + 1) h)).mpr
    rfl
  exact congrArg (attachmentEmbedding t.fragment (substitutionFragments σ t)) he

/-- An inserted cell port lies in its replacement occurrence's endpoint region. -/
theorem substitutionEmbedding_inserted (σ : ν → Term arity μ) (t : Term arity ν)
    (c : (t.subst σ).fragment.Cell)
    (d : Σ p : t.fragment.Leaf, (substitutionFragments σ t p).Cell)
    (h : substCellEquiv σ t c = .inr d)
    (p : Fin (arity ((t.subst σ).fragment.label c) + 1)) :
    substitutionEmbedding σ t (.inr ⟨c, p⟩) =
      .inr ⟨d.1, .inr ⟨d.2, Fin.cast (congrArg (fun a ↦ arity a + 1)
        (substitution_inserted_label σ t c d h).symm) p⟩⟩ := by
  have he : substitutionEndpoints σ t (.inr ⟨c, p⟩) =
      .inr ⟨.inr d, Fin.cast (congrArg (fun a ↦ arity a + 1)
        (substitution_inserted_label σ t c d h).symm) p⟩ := by
    apply congrArg Sum.inr
    apply Sigma.ext h
    apply (Fin.heq_ext_iff (congrArg
      (fun c ↦ arity (attachmentLabel t.fragment (substitutionFragments σ t) c) + 1) h)).mpr
    rfl
  exact congrArg (attachmentEmbedding t.fragment (substitutionFragments σ t)) he

/-- Beneath an agent, substitution's endpoint map agrees with the child's attachment embedding. -/
theorem substitutionEmbedding_child (σ : ν → Term arity μ) (a : α)
    (ts : Fin (arity a) → Term arity ν) (i : Fin (arity a))
    (p : Endpoint arity ((ts i).subst σ).fragment.label
      (Unit ⊕ ((ts i).subst σ).fragment.Leaf)) :
    substitutionEmbedding σ (agent a ts)
      (agentEndpointEquiv a (fun i ↦ ((ts i).subst σ).fragment) (.inr ⟨i, p⟩)) =
        childAttachmentEmbedding a (fun i ↦ (ts i).fragment)
          (substitutionFragments σ (agent a ts)) i (substitutionEmbedding σ (ts i) p) := by
  rcases p with (u | p) | ⟨c, p⟩
  · rfl
  · rfl
  · change substitutionEmbedding σ (agent a ts) (.inr ⟨.inr ⟨i, c⟩, p⟩) = _
    cases he : substCellEquiv σ (ts i) c with
    | inl d =>
      have hp : substCellEquiv σ (agent a ts) (.inr ⟨i, c⟩) = .inl (.inr ⟨i, d⟩) := by
        change substitutionCells (fun i ↦ (ts i).fragment.Cell)
          (fun i ↦ (ts i).fragment.Leaf)
          (fun i p ↦ (σ ((ts i).fragment.name p)).fragment.Cell)
          (.inr ⟨i, substCellEquiv σ (ts i) c⟩) = _
        rw [he]
        rfl
      exact (substitutionEmbedding_retained σ (agent a ts) _ _ hp p).trans
        (congrArg (childAttachmentEmbedding a (fun i ↦ (ts i).fragment)
          (substitutionFragments σ (agent a ts)) i)
          (substitutionEmbedding_retained σ (ts i) _ _ he p)).symm
    | inr d =>
      have hp : substCellEquiv σ (agent a ts) (.inr ⟨i, c⟩) = .inr ⟨⟨i, d.1⟩, d.2⟩ := by
        change substitutionCells (fun i ↦ (ts i).fragment.Cell)
          (fun i ↦ (ts i).fragment.Leaf)
          (fun i p ↦ (σ ((ts i).fragment.name p)).fragment.Cell)
          (.inr ⟨i, substCellEquiv σ (ts i) c⟩) = _
        rw [he]
        rfl
      exact (substitutionEmbedding_inserted σ (agent a ts) _ _ hp p).trans
        (congrArg (childAttachmentEmbedding a (fun i ↦ (ts i).fragment)
          (substitutionFragments σ (agent a ts)) i)
          (substitutionEmbedding_inserted σ (ts i) _ _ he p)).symm

/-- Execute the leaf-to-root attachment cuts without discarding their ambient endpoints. -/
def substitutionState (σ : ν → Term arity μ) (t : Term arity ν) :
    Wiring (AttachmentEndpoint t.fragment (substitutionFragments σ t)) × ℕ :=
  let : DecidableEq (AttachmentEndpoint t.fragment (substitutionFragments σ t)) :=
    attachmentDecidableEq t.fragment (substitutionFragments σ t)
  Wiring.glue (attachmentPorts t.fragment (substitutionFragments σ t)) t.fragment.order
    (attachmentState t.fragment (substitutionFragments σ t))

/-- Every wire of substituted syntax is represented by attachment of the replacement graphs. -/
theorem substitution_respects (σ : ν → Term arity μ) (t : Term arity ν) :
    Wiring.Respects (substitutionEmbedding σ t) (t.subst σ).fragment.net.wiring
      (substitutionState σ t).1 := by
  refine PFunctor.FreeM.rec (fun x ↦ ?_) (fun a ts ih ↦ ?_) t
  · have hw := attach_var_wiring x (σ x).fragment
    have hm : Wiring.Respects (substitutionEndpoints σ (var x)).toEmbedding
        (σ x).fragment.net.wiring
        ((TermFragment.var x).attach (fun _ ↦ (σ x).fragment)).net.wiring := by
      rw [← hw]
      exact Wiring.respects_map _ _
    exact hm.trans ((TermFragment.var x).attach_spec (fun _ ↦ (σ x).fragment)).1
  · intro p
    obtain ⟨q, rfl⟩ := (agentEndpointEquiv a (fun i ↦ (subst σ (ts i)).fragment)).surjective p
    rcases q with (u | v) | ⟨i, p⟩
    · change (substitutionState σ (agent a ts)).1.partner (.inl (.inl (.inl ()))) =
        .inl (.inr ⟨.inl (), 0⟩)
      apply Wiring.glue_keeps
      · intro i b; cases b <;> intro h <;> cases h
      · intro i b; cases b <;> intro h <;> cases h
      · rfl
    · change (substitutionState σ (agent a ts)).1.partner (.inl (.inr ⟨.inl (), 0⟩)) =
        .inl (.inl (.inl ()))
      apply Wiring.glue_keeps
      · intro i b; cases b <;> intro h <;> cases h
      · intro i b; cases b <;> intro h <;> cases h
      · rfl
    · have hh := (ih i).trans (childAttachment_glue a (fun i ↦ fragment (ts i))
        (substitutionFragments σ (agent a ts)) i)
      have hs := substitutionEmbedding_child σ a ts i p
      have ht := substitutionEmbedding_child σ a ts i
        ((subst σ (ts i)).fragment.net.wiring.partner p)
      have hp := Wiring.map_partner (agentEndpointEquiv a (fun i ↦ (subst σ (ts i)).fragment))
        (rootWire.sum (Wiring.sigma fun i ↦ (subst σ (ts i)).fragment.net.wiring)) (.inr ⟨i, p⟩)
      change ((fragment (subst σ (agent a ts))).net.wiring.partner
        (agentEndpointEquiv a (fun i ↦ (subst σ (ts i)).fragment) (.inr ⟨i, p⟩))) =
          agentEndpointEquiv a (fun i ↦ (subst σ (ts i)).fragment)
            (.inr ⟨i, (subst σ (ts i)).fragment.net.wiring.partner p⟩) at hp
      exact (congrArg (substitutionState σ (agent a ts)).1.partner hs).trans
        ((hh p).trans (ht.symm.trans (congrArg (substitutionEmbedding σ (agent a ts)) hp.symm)))

/-- Compiling a substituted term gives the same wires as attaching its replacement fragments. -/
theorem fragment_subst_wiring (σ : ν → Term arity μ) (t : Term arity ν) :
    (t.subst σ).fragment.net.wiring.map (substitutionEndpoints σ t) =
      (t.fragment.attach (substitutionFragments σ t)).net.wiring := by
  apply (substitution_respects σ t).map_eq
    (t.fragment.attach_spec (substitutionFragments σ t)).1 (substitutionEndpoints σ t)
  intro p
  rfl

/-- Both syntactic substitution and graph attachment have no closed wire component. -/
theorem fragment_subst_loops (σ : ν → Term arity μ) (t : Term arity ν) :
    (t.subst σ).fragment.net.loops = (t.fragment.attach (substitutionFragments σ t)).net.loops := by
  rw [attach_loops, fragment_loops, fragment_loops]
  simp only [substitutionFragments, fragment_loops, List.map_const', List.sum_replicate,
    Nat.zero_add]
  rfl

end Geb.InteractionNet.Term

end
