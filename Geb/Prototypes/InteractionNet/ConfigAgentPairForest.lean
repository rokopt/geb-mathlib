/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigHeadForest
public import Geb.Prototypes.InteractionNet.PairReconstruction
public import Geb.Prototypes.InteractionNet.BoundarySplice
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The open forest surrounding an agent equation

Removing the two root agents of a head equation exposes exactly their argument roots.
Their argument trees and the remaining configuration forest keep their cells, leaves
and boundary positions. Closing the head equation's root wire reconstructs the active
pair around this open forest.

## Main definitions

* {lit}`Config.agentPairBody` — the argument forest with the pair's auxiliary boundary exposed.

## Tags

interaction net, compiler, forest, agent, equation, active pair, context
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- The left then right auxiliary arguments of an agent equation, as open term fragments. -/
def agentArguments (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) (p : Boundary arity a b) : TermFragment arity ℕ :=
  (Sum.elim xs ys p).fragment

/-- Argument leaves and the remaining forest boundary survive removal of the two head roots. -/
abbrev AgentPairBoundary (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :=
  (Σ p, (agentArguments xs ys p).Leaf) ⊕ c.GraphForestBoundary

/-- Argument cells and the remaining forest cells survive removal of the two agents. -/
abbrev AgentPairCell (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :=
  (Σ p, (agentArguments xs ys p).Cell) ⊕ c.GraphCell

/-- Enumerate the retained boundaries using the argument and context occurrence positions. -/
@[instance_reducible] def agentPairBoundaryEnum (c : Config arity)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    FinEnum (c.AgentPairBoundary xs ys) :=
  let := sigmaEnum (C := fun p ↦ (agentArguments xs ys p).Leaf)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  inferInstance

/-- Enumerate the retained cells using their argument and context occurrence positions. -/
@[instance_reducible] def agentPairCellEnum (c : Config arity)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    FinEnum (c.AgentPairCell xs ys) :=
  let := sigmaEnum (C := fun p ↦ (agentArguments xs ys p).Cell)
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  inferInstance

/-- The original symbols on every retained argument and context cell. -/
def agentPairLabel (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) : c.AgentPairCell xs ys → α :=
  Sum.elim (fun p ↦ (agentArguments xs ys p.1).label p.2) c.graphLabel

/-- Separate the exposed argument roots from the surviving leaf and forest boundaries. -/
def agentArgumentsBoundaryEquiv (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    (Σ p, Unit ⊕ (agentArguments xs ys p).Leaf) ⊕ c.GraphForestBoundary ≃
      c.AgentPairBoundary xs ys ⊕ Boundary arity a b where
  toFun p := match p with
    | .inl ⟨p, .inl _⟩ => .inr p
    | .inl ⟨p, .inr q⟩ => .inl (.inl ⟨p, q⟩)
    | .inr q => .inl (.inr q)
  invFun p := match p with
    | .inl (.inl ⟨p, q⟩) => .inl ⟨p, .inr q⟩
    | .inl (.inr q) => .inr q
    | .inr p => .inl ⟨p, .inl ()⟩
  left_inv p := by rcases p with ⟨p, u | q⟩ | q <;> rfl
  right_inv p := by rcases p with (⟨p, q⟩ | q) | p <;> rfl

/-- Keep the argument graphs and remaining forest, exposing argument roots as auxiliary ports. -/
def agentPairBody (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    PortNet arity (c.agentPairLabel xs ys)
      (c.AgentPairBoundary xs ys ⊕ Boundary arity a b) :=
  ((PortNet.sigma (fun p ↦ (agentArguments xs ys p).net)).sum c.graphForest).reboundary
    (c.agentArgumentsBoundaryEquiv xs ys)

/-- Move the two head roots before the boundary positions that survive their closure. -/
def agentPairRootsEquiv (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    ((Unit ⊕ (Term.agent a xs).fragment.Leaf) ⊕
      ((Unit ⊕ (Term.agent b ys).fragment.Leaf) ⊕ c.GraphForestBoundary)) ≃
        Bool ⊕ c.AgentPairBoundary xs ys where
  toFun p := match p with
    | .inl (.inl _) => .inl false
    | .inr (.inl (.inl _)) => .inl true
    | .inl (.inr ⟨i, q⟩) => .inr (.inl ⟨.inl i, q⟩)
    | .inr (.inl (.inr ⟨i, q⟩)) => .inr (.inl ⟨.inr i, q⟩)
    | .inr (.inr q) => .inr (.inr q)
  invFun p := match p with
    | .inl false => .inl (.inl ())
    | .inl true => .inr (.inl (.inl ()))
    | .inr (.inl ⟨.inl i, q⟩) => .inl (.inr ⟨i, q⟩)
    | .inr (.inl ⟨.inr i, q⟩) => .inr (.inl (.inr ⟨i, q⟩))
    | .inr (.inr q) => .inr (.inr q)
  left_inv p := by rcases p with (u | ⟨i, q⟩) | ((u | ⟨i, q⟩) | q) <;> rfl
  right_inv p := by
    rcases p with bit | (⟨i | i, q⟩ | q)
    · cases bit <;> rfl
    · rfl
    · rfl
    · rfl

/-- Reorder the two agent cells before all retained argument and context cells. -/
def agentPairCellsEquiv (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    (Term.agent a xs).fragment.Cell ⊕
      ((Term.agent b ys).fragment.Cell ⊕ c.GraphCell) ≃
        Unit ⊕ (Unit ⊕ c.AgentPairCell xs ys) where
  toFun p := match p with
    | .inl (.inl _) => .inl ()
    | .inr (.inl (.inl _)) => .inr (.inl ())
    | .inl (.inr ⟨i, q⟩) => .inr (.inr (.inl ⟨.inl i, q⟩))
    | .inr (.inl (.inr ⟨i, q⟩)) => .inr (.inr (.inl ⟨.inr i, q⟩))
    | .inr (.inr q) => .inr (.inr (.inr q))
  invFun p := match p with
    | .inl _ => .inl (.inl ())
    | .inr (.inl _) => .inr (.inl (.inl ()))
    | .inr (.inr (.inl ⟨.inl i, q⟩)) => .inl (.inr ⟨i, q⟩)
    | .inr (.inr (.inl ⟨.inr i, q⟩)) => .inr (.inl (.inr ⟨i, q⟩))
    | .inr (.inr (.inr q)) => .inr (.inr q)
  left_inv p := by rcases p with (u | ⟨i, q⟩) | ((u | ⟨i, q⟩) | q) <;> rfl
  right_inv p := by rcases p with u | (v | (⟨i | i, q⟩ | q)) <;> rfl

/-- The head-agent and retained-cell decomposition preserves each agent symbol. -/
theorem agentPairCellsEquiv_label (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ)
    (p : (Term.agent a xs).fragment.Cell ⊕
      ((Term.agent b ys).fragment.Cell ⊕ c.GraphCell)) :
    PortNet.reconstructedLabel a b (c.agentPairLabel xs ys) (c.agentPairCellsEquiv xs ys p) =
      Sum.elim (Term.agent a xs).fragment.label
        (Sum.elim (Term.agent b ys).fragment.label c.graphLabel) p := by
  rcases p with (u | ⟨i, q⟩) | ((u | ⟨i, q⟩) | q) <;> rfl

private def pairForest (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :=
  (c.headForest (Term.agent a xs, Term.agent b ys)).reboundary (c.agentPairRootsEquiv xs ys)

private def bodyEmbedding (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    Endpoint arity (c.agentPairLabel xs ys) (c.AgentPairBoundary xs ys ⊕ Boundary arity a b) ↪
      Endpoint arity (Sum.elim (Term.agent a xs).fragment.label
        (Sum.elim (Term.agent b ys).fragment.label c.graphLabel))
          (Bool ⊕ c.AgentPairBoundary xs ys) :=
  Function.Embedding.inr.trans
    ((PortNet.reconstructionEndpointEquiv arity a b (c.agentPairLabel xs ys)).toEmbedding.trans
      ((endpointEquiv arity (Equiv.refl (c.AgentPairBoundary xs ys))
        (c.agentPairCellsEquiv xs ys) (c.agentPairCellsEquiv_label xs ys)).symm.toEmbedding.trans
          (Function.Embedding.sumMap .inr (.refl _))))

private def bodyAllocationEquiv (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    (Σ i, Endpoint arity (agentArguments xs ys i).label
      (Unit ⊕ (agentArguments xs ys i).Leaf)) ⊕
        Endpoint arity c.graphLabel c.GraphForestBoundary ≃
          Endpoint arity (c.agentPairLabel xs ys)
            (c.AgentPairBoundary xs ys ⊕ Boundary arity a b) :=
  (Equiv.sumCongr (PortNet.sigmaEndpointEquiv arity
    (fun i ↦ (agentArguments xs ys i).label)) (Equiv.refl _)).trans
      ((PortNet.sumEndpointEquiv arity
        (fun p : Σ i, (agentArguments xs ys i).Cell ↦ (agentArguments xs ys p.1).label p.2)
        c.graphLabel _ _).trans
          (endpointEquiv arity (c.agentArgumentsBoundaryEquiv xs ys) (Equiv.refl _)
            (fun _ ↦ rfl)))

private theorem bodyAllocation_wiring (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    ((Wiring.sigma (fun i ↦ (agentArguments xs ys i).net.wiring)).sum
      c.graphForest.wiring).map (bodyAllocationEquiv c xs ys) =
        (c.agentPairBody xs ys).wiring := by
  dsimp only [bodyAllocationEquiv]
  rw [Wiring.map_trans, Wiring.map_sum, Wiring.map_refl, Wiring.map_trans]
  rfl

private theorem child_respects (a : α) (f : Fin (arity a) → TermFragment arity ℕ)
    (i : Fin (arity a)) :
    Wiring.Respects ((Function.Embedding.sigmaMk i).trans
      (Function.Embedding.inr.trans (TermFragment.agentEndpointEquiv a f).toEmbedding))
        (f i).net.wiring (TermFragment.agent a f).net.wiring := by
  have h : Wiring.Respects (.sigmaMk i) (f i).net.wiring
      (Wiring.sigma (fun j ↦ (f j).net.wiring)) := fun _ ↦ rfl
  exact h.trans ((Wiring.respects_inr TermFragment.rootWire _).trans
    (Wiring.respects_map (TermFragment.agentEndpointEquiv a f) _))

private theorem bodyComponents_respects (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    Wiring.Respects ((bodyAllocationEquiv c xs ys).toEmbedding.trans (bodyEmbedding c xs ys))
      ((Wiring.sigma (fun i ↦ (agentArguments xs ys i).net.wiring)).sum c.graphForest.wiring)
      (pairForest c xs ys).wiring := by
  let left := (Term.agent a xs).fragment.net
  let right := (Term.agent b ys).fragment.net
  let e := endpointEquiv arity (label := Sum.elim (Term.agent a xs).fragment.label
    (Sum.elim (Term.agent b ys).fragment.label c.graphLabel))
      (c.agentPairRootsEquiv xs ys) (Equiv.refl _) (fun _ ↦ rfl)
  let er := PortNet.sumEndpointEquiv arity (Term.agent b ys).fragment.label c.graphLabel
    (Unit ⊕ (Term.agent b ys).fragment.Leaf) c.GraphForestBoundary
  let el := PortNet.sumEndpointEquiv arity (Term.agent a xs).fragment.label
    (Sum.elim (Term.agent b ys).fragment.label c.graphLabel)
      (Unit ⊕ (Term.agent a xs).fragment.Leaf)
      ((Unit ⊕ (Term.agent b ys).fragment.Leaf) ⊕ c.GraphForestBoundary)
  have hr := (Wiring.respects_inr left.wiring (right.sum c.graphForest).wiring).trans
    ((Wiring.respects_map el _).trans (Wiring.respects_map e _))
  have hl := (Wiring.respects_inl left.wiring (right.sum c.graphForest).wiring).trans
    ((Wiring.respects_map el _).trans (Wiring.respects_map e _))
  have hright := (Wiring.respects_inl right.wiring c.graphForest.wiring).trans
    ((Wiring.respects_map er _).trans hr)
  have hold := (Wiring.respects_inr right.wiring c.graphForest.wiring).trans
    ((Wiring.respects_map er _).trans hr)
  rintro (⟨i | i, p⟩ | p)
  · have h := (child_respects a (fun i ↦ (xs i).fragment) i).trans hl
    have he (q : Endpoint arity (xs i).fragment.label (Unit ⊕ (xs i).fragment.Leaf)) :
        bodyEmbedding c xs ys (bodyAllocationEquiv c xs ys (.inl ⟨.inl i, q⟩)) =
          ((Function.Embedding.sigmaMk i).trans
            (Function.Embedding.inr.trans (TermFragment.agentEndpointEquiv a
              (fun i ↦ (xs i).fragment)).toEmbedding)).trans
                (Function.Embedding.inl.trans (el.toEmbedding.trans e.toEmbedding)) q := by
      rcases q with (u | q) | ⟨v, p⟩ <;> rfl
    change (pairForest c xs ys).wiring.partner
      (bodyEmbedding c xs ys (bodyAllocationEquiv c xs ys (.inl ⟨.inl i, p⟩))) =
        bodyEmbedding c xs ys (bodyAllocationEquiv c xs ys
          (.inl ⟨.inl i, (xs i).fragment.net.wiring.partner p⟩))
    erw [he, he]
    exact h p
  · have h := (child_respects b (fun i ↦ (ys i).fragment) i).trans hright
    have he (q : Endpoint arity (ys i).fragment.label (Unit ⊕ (ys i).fragment.Leaf)) :
        bodyEmbedding c xs ys (bodyAllocationEquiv c xs ys (.inl ⟨.inr i, q⟩)) =
          ((Function.Embedding.sigmaMk i).trans
            (Function.Embedding.inr.trans (TermFragment.agentEndpointEquiv b
              (fun i ↦ (ys i).fragment)).toEmbedding)).trans
                (Function.Embedding.inl.trans (er.toEmbedding.trans
                  (Function.Embedding.inr.trans (el.toEmbedding.trans e.toEmbedding)))) q := by
      rcases q with (u | q) | ⟨v, p⟩ <;> rfl
    change (pairForest c xs ys).wiring.partner
      (bodyEmbedding c xs ys (bodyAllocationEquiv c xs ys (.inl ⟨.inr i, p⟩))) =
        bodyEmbedding c xs ys (bodyAllocationEquiv c xs ys
          (.inl ⟨.inr i, (ys i).fragment.net.wiring.partner p⟩))
    erw [he, he]
    exact h p
  · have he (p : Endpoint arity c.graphLabel c.GraphForestBoundary) :
        bodyEmbedding c xs ys (bodyAllocationEquiv c xs ys (.inr p)) =
          (Function.Embedding.inr.trans (er.toEmbedding.trans
            (Function.Embedding.inr.trans (el.toEmbedding.trans e.toEmbedding)))) p := by
      cases p <;> rfl
    change (pairForest c xs ys).wiring.partner
      (bodyEmbedding c xs ys (bodyAllocationEquiv c xs ys (.inr p))) =
        bodyEmbedding c xs ys (bodyAllocationEquiv c xs ys
          (.inr (c.graphForest.wiring.partner p)))
    erw [he, he]
    exact hold p

private theorem body_respects (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    Wiring.Respects (bodyEmbedding c xs ys) (c.agentPairBody xs ys).wiring
      (pairForest c xs ys).wiring := by
  have h := Wiring.respects_map (bodyAllocationEquiv c xs ys)
    ((Wiring.sigma (fun i ↦ (agentArguments xs ys i).net.wiring)).sum c.graphForest.wiring)
  rw [bodyAllocation_wiring] at h
  intro p
  obtain ⟨p, rfl⟩ := (bodyAllocationEquiv c xs ys).surjective p
  exact (bodyComponents_respects c xs ys p).trans
    (congrArg (bodyEmbedding c xs ys) (h p)).symm

/-- Term arguments and the remaining configuration forest contain no closed wire component. -/
theorem agentPairBody_loops (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) : (c.agentPairBody xs ys).loops = 0 := by
  simp [agentPairBody, PortNet.reboundary, PortNet.sum, PortNet.sigma, agentArguments,
    Term.fragment_loops, graphForest_loops]

/-- Closing the head roots preserves the reconstructed matching and creates no closed wire. -/
theorem agentPairForest_spec (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
    let := c.agentPairBoundaryEnum xs ys
    let n := ((c.headForest (Term.agent a xs, Term.agent b ys)).reboundary
      (c.agentPairRootsEquiv xs ys)).closeBoundaryPair
    n.wiring.map (endpointEquiv arity (Equiv.refl _) (c.agentPairCellsEquiv xs ys)
      (c.agentPairCellsEquiv_label xs ys)) =
        ((c.agentPairBody xs ys).reconstructPair a b).wiring ∧
      n.loops = (c.agentPairBody xs ys).loops := by
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := c.agentPairBoundaryEnum xs ys
  let := boolEnum
  let n := pairForest c xs ys
  let body := c.agentPairBody xs ys
  let e := endpointEquiv arity (Equiv.refl (c.AgentPairBoundary xs ys))
    (c.agentPairCellsEquiv xs ys) (c.agentPairCellsEquiv_label xs ys)
  let er := PortNet.reconstructionEndpointEquiv (Γ := c.AgentPairBoundary xs ys)
    arity a b (c.agentPairLabel xs ys)
  let retain : Endpoint arity (Sum.elim (Term.agent a xs).fragment.label
      (Sum.elim (Term.agent b ys).fragment.label c.graphLabel)) (c.AgentPairBoundary xs ys) ↪
        Endpoint arity (Sum.elim (Term.agent a xs).fragment.label
          (Sum.elim (Term.agent b ys).fragment.label c.graphLabel))
            (Bool ⊕ c.AgentPairBoundary xs ys) := Function.Embedding.sumMap .inr (.refl _)
  let : DecidableEq (Endpoint arity (Sum.elim (Term.agent a xs).fragment.label
      (Sum.elim (Term.agent b ys).fragment.label c.graphLabel))
        (Bool ⊕ c.AgentPairBoundary xs ys)) :=
    let : DecidableEq ((Term.agent a xs).fragment.Cell ⊕
      ((Term.agent b ys).fragment.Cell ⊕ c.GraphCell)) := FinEnum.decEq
    let : DecidableEq (c.AgentPairBoundary xs ys) := FinEnum.decEq
    inferInstanceAs (DecidableEq ((Bool ⊕ c.AgentPairBoundary xs ys) ⊕
      (Σ v, Fin (arity (Sum.elim (Term.agent a xs).fragment.label
        (Sum.elim (Term.agent b ys).fragment.label c.graphLabel) v) + 1))))
  have outside (p) (bit : Bool) : bodyEmbedding c xs ys p ≠ .inl (.inl bit) := by
    rcases p with ((⟨i | i, p⟩ | p) | (i | i)) | ⟨⟨i | i, q⟩ | q, p⟩ <;>
      intro h <;> cases h
  have hb : Wiring.Respects (bodyEmbedding c xs ys) body.wiring
      (n.wiring.force (.inl (.inl false)) (.inl (.inl true))) := by
    intro p
    exact Wiring.force_keeps _ (by intro h; cases h)
      (outside p false) (outside p true)
      (outside (body.wiring.partner p) false) (outside (body.wiring.partner p) true)
      (body_respects c xs ys p)
  have hr : Wiring.Respects (er.toEmbedding.trans (e.symm.toEmbedding.trans retain))
      (TermFragment.rootWire.sum body.wiring)
      (n.wiring.force (.inl (.inl false)) (.inl (.inl true))) := by
    rintro ((u | v) | p)
    · exact n.wiring.force_partner_left (a := .inl (.inl false))
        (b := .inl (.inl true)) (by intro h; cases h)
    · exact n.wiring.force_partner_right (a := .inl (.inl false))
        (b := .inl (.inl true)) (by intro h; cases h)
    · exact hb p
  have hs := (Wiring.respects_map_symm er (TermFragment.rootWire.sum body.wiring)).trans hr
  have he : er.symm.toEmbedding.trans (er.toEmbedding.trans (e.symm.toEmbedding.trans retain)) =
      e.symm.toEmbedding.trans retain := by
    ext p
    change retain (e.symm (er (er.symm p))) = retain (e.symm p)
    rw [Equiv.apply_symm_apply]
  rw [he] at hs
  have hc := n.closeBoundaryPair_spec
  refine ⟨?_, ?_⟩
  · exact hc.map_eq hs e (fun p ↦ by
      change retain p = retain (e.symm (e p))
      rw [Equiv.symm_apply_apply])
  · change n.closeBoundaryPair.loops = body.loops
    rw [n.closeBoundaryPair_loops, agentPairBody_loops]
    have hn : n.loops = 0 := by
      change (c.headForest (Term.agent a xs, Term.agent b ys)).loops = 0
      rw [headForest_loops, graphForest_loops]
    rw [hn]
    rfl

/-- Closing the head roots reconstructs exactly the pair around its open argument forest. -/
def agentPairForestIso (c : Config arity) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) :
    let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
    let := c.agentPairBoundaryEnum xs ys
    (((c.headForest (Term.agent a xs, Term.agent b ys)).reboundary
      (c.agentPairRootsEquiv xs ys)).closeBoundaryPair).Iso
        ((c.agentPairBody xs ys).reconstructPair a b) :=
  ⟨c.agentPairCellsEquiv xs ys, c.agentPairCellsEquiv_label xs ys,
    (c.agentPairForest_spec xs ys).1, (c.agentPairForest_spec xs ys).2⟩

end Geb.InteractionNet.Config

end
