/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigEliminationAllocation
public import Geb.Prototypes.InteractionNet.BoundarySplice
public import Geb.Prototypes.InteractionNet.ForestAttachment
public import Geb.Prototypes.InteractionNet.PortNetSum
public import Geb.Prototypes.InteractionNet.WiringRelocation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Cancelling variable replacements in an elimination forest

Only the selected occurrence inserts a term graph. At every other occurrence, attachment
extends a wire through a variable fragment. Cancelling those extensions leaves the original
forest and one replacement, joined at the selected leaf and replacement root.

## Tags

interaction net, compiler, elimination, substitution, forest, wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

private abbrev Ambient (c : Config arity) (x : ℕ) (t : Term arity ℕ) :=
  TermFragment.ForestAttachmentEndpoint c.graphFragments (c.eliminationFragments x t)

private abbrev OldEndpoint (c : Config arity) :=
  Σ i, Endpoint arity (c.graphFragments i).label (Unit ⊕ (c.graphFragments i).Leaf)

private abbrev InsertedEndpoint (t : Term arity ℕ) :=
  Endpoint arity t.fragment.label (Unit ⊕ t.fragment.Leaf)

private def separateEmbedding (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x) :
    InsertedEndpoint t ⊕ OldEndpoint c ↪ Ambient c x t where
  toFun q := match q with
    | .inl q => ⟨p.1, .inr ⟨p.2, (Term.fragmentEndpointEquiv (ite_eq_left hp)).symm q⟩⟩
    | .inr ⟨i, q⟩ => ⟨i, .inl q⟩
  inj' := by
    rintro (q | ⟨i, q⟩) (r | ⟨j, r⟩) h
    · apply congrArg Sum.inl
      apply (Term.fragmentEndpointEquiv (ite_eq_left hp)).symm.injective
      exact eq_of_heq (Sigma.mk.inj_iff.mp
        (Sum.inr.inj (eq_of_heq (Sigma.mk.inj_iff.mp h).2))).2
    · have he : p.1 = j := congrArg Sigma.fst h
      subst j
      cases eq_of_heq (Sigma.mk.inj_iff.mp h).2
    · have he : i = p.1 := congrArg Sigma.fst h
      subst i
      cases eq_of_heq (Sigma.mk.inj_iff.mp h).2
    · have he : i = j := congrArg Sigma.fst h
      subst j
      exact congrArg (fun q ↦ Sum.inr (Sigma.mk i q))
        (Sum.inl.inj (eq_of_heq (Sigma.mk.inj_iff.mp h).2))

private def start (c : Config arity) (x : ℕ) (t : Term arity ℕ) :
    Wiring (Ambient c x t) × ℕ :=
  TermFragment.forestAttachmentState c.graphFragments (c.eliminationFragments x t)

private theorem separate_respects (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x) :
    Wiring.Respects (separateEmbedding c x t p hp)
      (t.fragment.net.wiring.sum (Wiring.sigma fun i ↦ (c.graphFragments i).net.wiring))
      (start c x t).1 := by
  rintro (q | ⟨i, q⟩)
  · have h := Wiring.respects_map_symm (Term.fragmentEndpointEquiv
      (s := if c.graphLeafName p = x then t else Term.var (c.graphLeafName p))
        (ite_eq_left hp)) (c.eliminationFragments x t p.1 p.2).net.wiring
    erw [Term.fragmentEndpointEquiv_wiring] at h
    exact congrArg (fun q ↦ (Sigma.mk p.1 (Sum.inr (Sigma.mk p.2 q)) : Ambient c x t)) (h q)
  · rfl

private def baseEmbedding (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x) :
    Endpoint arity (Sum.elim t.fragment.label c.graphLabel)
      ((Unit ⊕ t.fragment.Leaf) ⊕ c.GraphForestBoundary) ↪ Ambient c x t :=
  (PortNet.sumEndpointEquiv arity t.fragment.label c.graphLabel
    (Unit ⊕ t.fragment.Leaf) c.GraphForestBoundary).symm.toEmbedding.trans
      ((Function.Embedding.sumMap (.refl _)
        (PortNet.sigmaEndpointEquiv arity
          (fun i ↦ (c.graphFragments i).label)).symm.toEmbedding).trans
          (separateEmbedding c x t p hp))

private theorem base_respects (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x) :
    Wiring.Respects (baseEmbedding c x t p hp) (t.fragment.net.sum c.graphForest).wiring
      (start c x t).1 := by
  exact (Wiring.respects_map_symm
    (PortNet.sumEndpointEquiv arity t.fragment.label c.graphLabel
      (Unit ⊕ t.fragment.Leaf) c.GraphForestBoundary) _).trans
        (((Wiring.respects_refl t.fragment.net.wiring).sum
          (Wiring.respects_map_symm (PortNet.sigmaEndpointEquiv arity
            (fun i ↦ (c.graphFragments i).label)) _)).trans (separate_respects c x t p hp))

private def ports (c : Config arity) (x : ℕ) (t : Term arity ℕ) :
    c.GraphLeaf × Bool ↪ Ambient c x t :=
  TermFragment.forestAttachmentPorts c.graphFragments (c.eliminationFragments x t)

private def ambientDecidableEq (c : Config arity) (x : ℕ) (t : Term arity ℕ) :
    DecidableEq (Ambient c x t) :=
  TermFragment.forestAttachmentDecidableEq c.graphFragments (c.eliminationFragments x t)

private local instance (c : Config arity) (x : ℕ) (t : Term arity ℕ) :
    DecidableEq (Ambient c x t) := ambientDecidableEq c x t

private theorem replacement_free (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (i j : c.GraphLeaf) (b : Bool) :
    (start c x t).1.partner (ports c x t (i, true)) ≠ ports c x t (j, b) := by
  intro h
  have he : i.1 = j.1 := congrArg (fun q : Ambient c x t ↦ q.1) h
  rcases i with ⟨i, q⟩
  rcases j with ⟨j, r⟩
  dsimp only at he
  subst j
  have h := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  cases b with
  | false => cases h
  | true =>
    have he : q = r := congrArg Sigma.fst (Sum.inr.inj h)
    subst r
    exact (c.eliminationFragments x t i q).net.wiring.fixedPointFree (.inl (.inl ()))
      (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2)

private def variableOrder (c : Config arity) (x : ℕ) :=
  (TermFragment.forestOrder (FinEnum.toList c.GraphRoot) c.graphFragments).filter
    (fun q ↦ decide (c.graphLeafName q ≠ x))

private theorem variableOrder_unique (c : Config arity) (x : ℕ) :
    (variableOrder c x).Nodup :=
  (TermFragment.forestOrder_unique _ FinEnum.nodup_toList c.graphFragments).filter _

private theorem mem_variableOrder (c : Config arity) (x : ℕ) (q : c.GraphLeaf) :
    q ∈ variableOrder c x ↔ c.graphLeafName q ≠ x := by
  have h := TermFragment.forestOrder_cover (FinEnum.toList c.GraphRoot)
    FinEnum.mem_toList c.graphFragments q
  simp only [variableOrder, List.mem_filter, h, decide_eq_true_eq, true_and]

private def relocate (c : Config arity) (x : ℕ) (t : Term arity ℕ) :
    Equiv.Perm (Ambient c x t) :=
  (start c x t).1.relocation (ports c x t) (variableOrder c x) true

private theorem cancel_variables (c : Config arity) (x : ℕ) (t : Term arity ℕ) :
    Wiring.glue (ports c x t) (variableOrder c x) (start c x t) =
      ((start c x t).1.map (relocate c x t), (start c x t).2) :=
  Wiring.glue_relocation (ports c x t) (variableOrder c x) (variableOrder_unique c x)
    (start c x t).1 (start c x t).2 true (fun i _ j _ b ↦ replacement_free c x t i j b)

private def replacementIndex (c : Config arity) (x : ℕ) (t : Term arity ℕ) :
    Ambient c x t → Option c.GraphLeaf
  | ⟨_, .inl _⟩ => none
  | ⟨i, .inr ⟨q, _⟩⟩ => some ⟨i, q⟩

private theorem relocate_inserted (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (q : Endpoint arity (c.eliminationFragments x t p.1 p.2).label
      (Unit ⊕ (c.eliminationFragments x t p.1 p.2).Leaf)) :
    relocate c x t ⟨p.1, .inr ⟨p.2, q⟩⟩ = ⟨p.1, .inr ⟨p.2, q⟩⟩ := by
  apply Wiring.relocation_apply_of_outside
  intro i hi
  constructor
  · intro h
    have he := congrArg (replacementIndex c x t) h
    cases he
  · intro h
    have he : p = i := Option.some.inj (congrArg (replacementIndex c x t) h)
    exact (mem_variableOrder c x i).mp hi (he ▸ hp)

private theorem relocate_root (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (i : c.GraphRoot) :
    relocate c x t ⟨i, .inl (.inl (.inl ()))⟩ = ⟨i, .inl (.inl (.inl ()))⟩ := by
  apply Wiring.relocation_apply_of_outside
  intro j _
  constructor
  · intro h
    have he : i = j.1 := congrArg Sigma.fst h
    rcases j with ⟨j, q⟩
    dsimp only at he
    subst j
    cases eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · intro h
    have he := congrArg (replacementIndex c x t) h
    cases he

private theorem relocate_cell (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (i : c.GraphRoot) (q : CellPort arity (c.graphFragments i).label) :
    relocate c x t ⟨i, .inl (.inr q)⟩ = ⟨i, .inl (.inr q)⟩ := by
  apply Wiring.relocation_apply_of_outside
  intro j _
  constructor
  · intro h
    have he : i = j.1 := congrArg Sigma.fst h
    rcases j with ⟨j, r⟩
    dsimp only at he
    subst j
    cases eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · intro h
    have he := congrArg (replacementIndex c x t) h
    cases he

private theorem relocate_leaf (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p ≠ x) :
    relocate c x t (ports c x t (p, false)) = (start c x t).1.partner (ports c x t (p, true)) := by
  have h := Wiring.relocation_apply_cut (start c x t).1 (ports c x t)
    (variableOrder c x) (variableOrder_unique c x) true (replacement_free c x t) p
  rw [ite_eq_left ((mem_variableOrder c x p).mpr hp)] at h
  exact h

private theorem relocate_selected_leaf (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x) :
    relocate c x t (ports c x t (p, false)) = ports c x t (p, false) := by
  have h := Wiring.relocation_apply_cut (start c x t).1 (ports c x t)
    (variableOrder c x) (variableOrder_unique c x) true (replacement_free c x t) p
  rw [ite_eq_right (fun h ↦ (mem_variableOrder c x p).mp h hp)] at h
  exact h

private theorem variable_partner (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p ≠ x) :
    (start c x t).1.partner (ports c x t (p, true)) =
      ⟨p.1, .inr ⟨p.2, .inl (.inr ((Term.fragmentLeafEquiv (ite_eq_right hp)).symm
        (Term.fragmentVarLeaf (c.graphLeafName p))))⟩⟩ := by
  have h := Wiring.respects_map_symm (Term.fragmentEndpointEquiv
    (s := if c.graphLeafName p = x then t else Term.var (c.graphLeafName p))
      (ite_eq_right hp)) (c.eliminationFragments x t p.1 p.2).net.wiring
  erw [Term.fragmentEndpointEquiv_wiring] at h
  exact congrArg (fun q ↦ (Sigma.mk p.1 (Sum.inr (Sigma.mk p.2 q)) : Ambient c x t))
    (h (.inl (.inl ())))

/-- Enumerate the exposed forest boundary using its explicit occurrence correspondence. -/
@[instance_reducible] def eliminationBoundaryEnum (c : Config arity) (x : ℕ)
    (t : Term arity ℕ) (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) : FinEnum (c.EliminationBoundary x t) :=
  let := sigmaEnum (C := fun i ↦
    Unit ⊕ ((c.graphFragments i).attach (c.eliminationFragments x t i)).Leaf)
  FinEnum.ofEquiv _ (c.eliminationForestBoundaryEquiv x t p hp unique).symm

private def openNet (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    PortNet arity (Sum.elim t.fragment.label c.graphLabel) (Bool ⊕ c.EliminationBoundary x t) :=
  (t.fragment.net.sum c.graphForest).reboundary
    (c.eliminationOpenBoundaryEquiv x t p hp unique)

/-- Join the one inserted term to its selected leaf in the retained forest. -/
def eliminationJoinedForest (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    PortNet arity (Sum.elim t.fragment.label c.graphLabel) (c.EliminationBoundary x t) :=
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := c.eliminationBoundaryEnum x t p hp unique
  ((t.fragment.net.sum c.graphForest).reboundary
    (c.eliminationOpenBoundaryEquiv x t p hp unique)).closeBoundaryPair

private def openEmbedding (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    Endpoint arity (Sum.elim t.fragment.label c.graphLabel)
      (Bool ⊕ c.EliminationBoundary x t) ↪ Ambient c x t :=
  (endpointEquiv arity (c.eliminationOpenBoundaryEquiv x t p hp unique)
    (Equiv.refl _) (fun _ ↦ rfl)).symm.toEmbedding.trans (baseEmbedding c x t p hp)

private theorem open_respects (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    Wiring.Respects (openEmbedding c x t p hp unique) (openNet c x t p hp unique).wiring
      (start c x t).1 :=
  (Wiring.respects_map_symm (endpointEquiv arity
    (c.eliminationOpenBoundaryEquiv x t p hp unique) (Equiv.refl _) (fun _ ↦ rfl)) _).trans
      (base_respects c x t p hp)

private def closedEmbedding (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    Endpoint arity (Sum.elim t.fragment.label c.graphLabel) (c.EliminationBoundary x t) ↪
      Ambient c x t :=
  (Function.Embedding.sumMap .inr (.refl _)).trans
    ((openEmbedding c x t p hp unique).trans (relocate c x t).toEmbedding)

private theorem joined_respects (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    Wiring.Respects (closedEmbedding c x t p hp unique)
      (c.eliminationJoinedForest x t p hp unique).wiring
      (((start c x t).1.map (relocate c x t)).force
        (ports c x t (p, false)) (ports c x t (p, true))) := by
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := c.eliminationBoundaryEnum x t p hp unique
  let := boolEnum
  let : DecidableEq (Endpoint arity (Sum.elim t.fragment.label c.graphLabel)
      (Bool ⊕ c.EliminationBoundary x t)) :=
    let : DecidableEq (t.fragment.Cell ⊕ c.GraphCell) := FinEnum.decEq
    let : DecidableEq (c.EliminationBoundary x t) := FinEnum.decEq
    inferInstanceAs (DecidableEq ((Bool ⊕ c.EliminationBoundary x t) ⊕
      (Σ d, Fin (arity (Sum.elim t.fragment.label c.graphLabel d) + 1))))
  have hs := (openNet c x t p hp unique).closeBoundaryPair_spec
  have he := (open_respects c x t p hp unique).trans
    (Wiring.respects_map (relocate c x t) (start c x t).1)
  have hf := he.force (a := .inl (.inl false)) (b := .inl (.inl true))
    (by intro h; cases h)
  have hl : (openEmbedding c x t p hp unique).trans (relocate c x t).toEmbedding
      (.inl (.inl false)) = ports c x t (p, false) :=
    relocate_selected_leaf c x t p hp
  have hr : (openEmbedding c x t p hp unique).trans (relocate c x t).toEmbedding
      (.inl (.inl true)) = ports c x t (p, true) :=
    relocate_inserted c x t p hp (.inl (.inl ()))
  erw [hl, hr] at hf
  exact hs.trans hf

private theorem attachment_order (c : Config arity) (x : ℕ) (p : c.GraphLeaf)
    (hp : c.graphLeafName p = x) (unique : ∀ q, c.graphLeafName q = x → q = p) :
    (TermFragment.forestOrder (FinEnum.toList c.GraphRoot) c.graphFragments).Perm
      (variableOrder c x ++ [p]) := by
  let := c.graphLeafEnum
  have h := Wiring.enum_perm_of_cover (order := variableOrder c x ++ [p]) ?_ ?_
  · have h' := Wiring.enum_perm_of_cover
      (order := TermFragment.forestOrder (FinEnum.toList c.GraphRoot) c.graphFragments)
        (TermFragment.forestOrder_unique _ FinEnum.nodup_toList c.graphFragments)
        (TermFragment.forestOrder_cover _ FinEnum.mem_toList c.graphFragments)
    exact h'.symm.trans h
  · rw [List.nodup_append]
    refine ⟨variableOrder_unique c x, by simp, ?_⟩
    intro q hq r hr he
    have hr : r = p := List.mem_singleton.mp hr
    subst r
    subst q
    exact (mem_variableOrder c x p).mp hq hp
  · intro q
    by_cases hq : c.graphLeafName q = x
    · exact List.mem_append_right _ (List.mem_singleton.mpr (unique q hq))
    · exact List.mem_append_left _ ((mem_variableOrder c x q).mpr hq)

private theorem attached_respects (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    Wiring.Respects (TermFragment.forestAttachmentEmbedding c.graphFragments
      (c.eliminationFragments x t))
      (PortNet.sigma (fun i ↦ ((c.graphFragments i).attach
        (c.eliminationFragments x t i)).net)).wiring
      (((start c x t).1.map (relocate c x t)).force
        (ports c x t (p, false)) (ports c x t (p, true))) := by
  have h := (TermFragment.forestAttach_spec c.graphFragments (c.eliminationFragments x t)).1
  change Wiring.Respects _ _ (Wiring.glue (ports c x t)
    (TermFragment.forestOrder (FinEnum.toList c.GraphRoot) c.graphFragments) (start c x t)).1 at h
  rw [Wiring.glue_perm _ (attachment_order c x p hp unique)] at h
  simp only [Wiring.glue, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
  change Wiring.Respects _ _ (Wiring.glueAt (ports c x t)
    (Wiring.glue (ports c x t) (variableOrder c x) (start c x t)) p).1 at h
  rw [cancel_variables] at h
  exact h

private def forestEndpointsEquiv (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :=
  endpointEquiv arity (c.eliminationForestBoundaryEquiv x t p hp unique)
    (c.eliminationForestCellsEquiv x t p hp unique)
    (c.eliminationForestCellsEquiv_label x t p hp unique)

private theorem endpoint_agreement (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (q : Endpoint arity
      (fun d : Σ i, ((c.graphFragments i).attach (c.eliminationFragments x t i)).Cell ↦
        ((c.graphFragments d.1).attach (c.eliminationFragments x t d.1)).label d.2)
      (Σ i, Unit ⊕ ((c.graphFragments i).attach (c.eliminationFragments x t i)).Leaf)) :
    TermFragment.forestAttachmentEmbedding c.graphFragments (c.eliminationFragments x t) q =
      closedEmbedding c x t p hp unique (forestEndpointsEquiv c x t p hp unique q) := by
  rcases q with ⟨i, u | ⟨j, q⟩⟩ | ⟨⟨i, q | ⟨j, q⟩⟩, a⟩
  · exact (relocate_root c x t i).symm
  · by_cases hq : c.graphLeafName ⟨i, j⟩ = x
    · have he := unique ⟨i, j⟩ hq
      subst p
      change (Sigma.mk i (Sum.inr (Sigma.mk j (Sum.inl (Sum.inr q)))) : Ambient c x t) =
        closedEmbedding c x t ⟨i, j⟩ hp unique
          (.inl (c.eliminationForestBoundaryEquiv x t ⟨i, j⟩ hp unique ⟨i, .inr ⟨j, q⟩⟩))
      have hb : c.eliminationForestBoundaryEquiv x t ⟨i, j⟩ hp unique ⟨i, .inr ⟨j, q⟩⟩ =
          .inr (.inl (Term.fragmentLeafEquiv (ite_eq_left hq) q)) := by
        change Sum.inr (if h : c.graphLeafName ⟨i, j⟩ = x then _ else _) = _
        rw [dite_eq_left hq]
        rfl
      rw [hb]
      change _ = relocate c x t ⟨i, .inr ⟨j, .inl (.inr
        ((Term.fragmentLeafEquiv (ite_eq_left hq)).symm
          (Term.fragmentLeafEquiv (ite_eq_left hq) q)))⟩⟩
      erw [Equiv.symm_apply_apply, relocate_inserted c x t ⟨i, j⟩ hq]
    · have hb : c.eliminationForestBoundaryEquiv x t p hp unique ⟨i, .inr ⟨j, q⟩⟩ =
          .inr (.inr ⟨⟨i, j⟩, hq⟩) := by
        change Sum.inr (if h : c.graphLeafName ⟨i, j⟩ = x then _ else _) = _
        rw [dite_eq_right hq]
      change (Sigma.mk i (Sum.inr (Sigma.mk j (Sum.inl (Sum.inr q)))) : Ambient c x t) =
        closedEmbedding c x t p hp unique
          (.inl (c.eliminationForestBoundaryEquiv x t p hp unique ⟨i, .inr ⟨j, q⟩⟩))
      rw [hb]
      change _ = relocate c x t (ports c x t (⟨i, j⟩, false))
      rw [relocate_leaf c x t ⟨i, j⟩ hq, variable_partner c x t ⟨i, j⟩ hq]
      have hl : q = (Term.fragmentLeafEquiv (ite_eq_right hq)).symm
          (Term.fragmentVarLeaf (c.graphLeafName ⟨i, j⟩)) := by
        apply (Term.fragmentLeafEquiv (ite_eq_right hq)).injective
        erw [Equiv.apply_symm_apply]
      rw [hl]
      rfl
  · exact (relocate_cell c x t i ⟨q, a⟩).symm
  · by_cases hq : c.graphLeafName ⟨i, j⟩ = x
    · have he := unique ⟨i, j⟩ hq
      subst p
      have hc : c.eliminationForestCellsEquiv x t ⟨i, j⟩ hp unique ⟨i, .inr ⟨j, q⟩⟩ =
          .inl (Term.fragmentCellEquiv (ite_eq_left hq) q) := by
        change Sum.inl (if h : c.graphLeafName ⟨i, j⟩ = x then _ else _) = _
        rw [dite_eq_left hq]
        rfl
      let v := Fin.cast (congrArg (fun b ↦ arity b + 1)
        (Term.fragment_label_cast (ite_eq_left hq) q).symm) a
      have hc' : forestEndpointsEquiv c x t ⟨i, j⟩ hp unique
          (.inr ⟨⟨i, .inr ⟨j, q⟩⟩, a⟩) =
            .inr ⟨.inl (Term.fragmentCellEquiv (ite_eq_left hq) q), v⟩ := by
        apply congrArg Sum.inr
        apply Sigma.ext hc
        exact (Fin.heq_ext_iff (congrArg (fun b ↦ arity b + 1)
          ((c.eliminationForestCellsEquiv_label x t ⟨i, j⟩ hp unique ⟨i, .inr ⟨j, q⟩⟩).trans
            (Term.fragment_label_cast (ite_eq_left hq) q).symm))).mpr rfl
      rw [hc']
      change (Sigma.mk i (Sum.inr (Sigma.mk j (Sum.inr ⟨q, a⟩))) : Ambient c x t) =
        relocate c x t ⟨i, .inr ⟨j,
          (Term.fragmentEndpointEquiv (ite_eq_left hq)).symm
            (Term.fragmentEndpointEquiv (ite_eq_left hq) (.inr ⟨q, a⟩))⟩⟩
      erw [Equiv.symm_apply_apply, relocate_inserted c x t ⟨i, j⟩ hq]
      rfl
    · exact Fin.elim0 (Term.fragmentCellEquiv (ite_eq_right hq) q)

/-- Cancelling variable extensions leaves exactly the selected leaf-to-root attachment. -/
theorem eliminationForest_wiring (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    (PortNet.sigma (fun i ↦ ((c.graphFragments i).attach
      (c.eliminationFragments x t i)).net)).wiring.map
        (endpointEquiv arity (c.eliminationForestBoundaryEquiv x t p hp unique)
          (c.eliminationForestCellsEquiv x t p hp unique)
          (c.eliminationForestCellsEquiv_label x t p hp unique)) =
            (c.eliminationJoinedForest x t p hp unique).wiring :=
  (attached_respects c x t p hp unique).map_eq (joined_respects c x t p hp unique)
    (forestEndpointsEquiv c x t p hp unique) (endpoint_agreement c x t p hp unique)

/-- Joining separate term and context fragments creates no closed wire. -/
theorem eliminationJoinedForest_loops (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    (c.eliminationJoinedForest x t p hp unique).loops = 0 := by
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := c.eliminationBoundaryEnum x t p hp unique
  let := boolEnum
  have hn : (openNet c x t p hp unique).wiring.partner (.inl (.inl false)) ≠
      .inl (.inl true) := by
    intro h
    have he := open_respects c x t p hp unique (.inl (.inl false))
    rw [h] at he
    have hi := congrArg (replacementIndex c x t) he
    cases hi
  change (openNet c x t p hp unique).closeBoundaryPair.loops = 0
  rw [PortNet.closeBoundaryPair_loops]
  simp only [Wiring.loopDelta, hn, ↓reduceIte, Nat.add_zero]
  exact (congrArg₂ (· + ·) (Term.fragment_loops t) c.graphForest_loops).trans (Nat.zero_add 0)

/-- The full attachment forest and the single joined replacement have the same closed wires. -/
theorem eliminationForest_loops (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    (PortNet.sigma (fun i ↦ ((c.graphFragments i).attach
      (c.eliminationFragments x t i)).net)).loops =
        (c.eliminationJoinedForest x t p hp unique).loops := by
  rw [eliminationJoinedForest_loops]
  have hz (i : c.GraphRoot) : (c.graphFragments i).net.loops = 0 := by
    rw [graphFragments_term]
    exact Term.fragment_loops _
  have hr (i : c.GraphRoot) (q : (c.graphFragments i).Leaf) :
      (c.eliminationFragments x t i q).net.loops = 0 := Term.fragment_loops _
  simp [PortNet.sigma, TermFragment.attach_loops, hz, hr]

end Geb.InteractionNet.Config

end
