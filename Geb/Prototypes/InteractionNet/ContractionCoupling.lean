/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.AssemblyEmbedding
public import Geb.Prototypes.InteractionNet.ContractionEmbedding
public import Geb.Prototypes.InteractionNet.CouplingWires
public import Geb.Prototypes.InteractionNet.FiniteCells
public import Geb.Prototypes.InteractionNet.WiringCompose
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Contraction inside a boundary context

An active pair already present in a net survives attachment of a boundary matching.
Contracting that pair before or after the attachment gives the same net, with the same
surviving and replacement cells. The two operations splice disjoint endpoint families;
their commutation therefore preserves both partners and closed-wire counts.

## Main statements

* {lit}`PortNet.couple_active` — boundary attachment preserves an existing active pair.
* {lit}`PortNet.contract_couple` — contraction commutes with boundary attachment.

## Tags

interaction net, compiler, graph, contraction, context, boundary, closed wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

variable {α C D B Γ : Type} {arity : α → ℕ} {label : C → α} {label' : D → α}
variable [FinEnum C] [FinEnum D] [FinEnum B] [FinEnum Γ]

/-- Attaching a boundary matching preserves every existing principal-to-principal wire. -/
theorem couple_active (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    {a b : C} (h : n.Active a b) : (n.couple w).Active a b :=
  n.couple_internal_wire w ⟨a, 0⟩ ⟨b, 0⟩ h

private abbrev Ambient (arity : α → ℕ) (label : C → α) (label' : D → α)
    (B Γ : Type) (a b : C) :=
  (Γ ⊕ B) ⊕ (Endpoint arity label B ⊕ Endpoint arity label' (PairBoundary arity label a b))

private def contextEmbedding (a b : C) :
    CouplingEndpoint arity label Γ B ↪ Ambient arity label label' B Γ a b :=
  Function.Embedding.sumMap (.refl _) .inl

private def boundaryPorts (a b : C) : B × Bool ↪ Ambient arity label label' B Γ a b :=
  (couplePorts arity label Γ B).trans (contextEmbedding a b)

private def pairPorts {a b : C} (hab : a ≠ b) :
    PairBoundary arity label a b × Bool ↪ Ambient arity label label' B Γ a b :=
  (contractPorts arity label label' hab).trans .inr

omit [FinEnum D] [FinEnum B] [FinEnum Γ] in
private theorem disjoint_ports {a b : C} (hab : a ≠ b) (i : B) (x : Bool)
    (j : PairBoundary arity label a b) (y : Bool) :
    boundaryPorts (arity := arity) (label := label) (label' := label') (Γ := Γ) a b (i, x) ≠
      pairPorts hab (j, y) := by
  cases j <;> cases x <;> cases y <;> intro h <;> cases h

private def afterContract {a b : C} (hab : a ≠ b) :
    CouplingEndpoint arity (Sum.elim (fun c : RemainingCell a b ↦ label c) label') Γ B ↪
      Ambient arity label label' B Γ a b :=
  Function.Embedding.sumMap (.refl _) (contractEmbedding arity label label' hab)

private def afterContext (a b : C) :
    Endpoint arity label Γ ⊕ Endpoint arity label' (PairBoundary arity label a b) ↪
      Ambient arity label label' B Γ a b where
  toFun p := match p with
    | .inl (.inl γ) => .inl (.inl γ)
    | .inl (.inr p) => .inr (.inl (.inr p))
    | .inr p => .inr (.inr p)
  inj' := by
    rintro ((γ | p) | q) ((δ | r) | s) h <;> simp_all

private def finalEmbedding {a b : C} (hab : a ≠ b) :
    Endpoint arity (Sum.elim (fun c : RemainingCell a b ↦ label c) label') Γ ↪
      Ambient arity label label' B Γ a b :=
  (contractEmbedding arity label label' hab).trans (afterContext a b)

variable {a b : C}

private def ambientDecidableEq : DecidableEq (Ambient arity label label' B Γ a b) :=
  let : DecidableEq C := FinEnum.decEq
  let : DecidableEq D := FinEnum.decEq
  let : DecidableEq B := FinEnum.decEq
  let : DecidableEq Γ := FinEnum.decEq
  let : DecidableEq (Endpoint arity label B) :=
    inferInstanceAs (DecidableEq (B ⊕ (Σ c : C, Fin (arity (label c) + 1))))
  let : DecidableEq (Endpoint arity label' (PairBoundary arity label a b)) :=
    inferInstanceAs (DecidableEq ((Fin (arity (label a)) ⊕ Fin (arity (label b))) ⊕
      (Σ d : D, Fin (arity (label' d) + 1))))
  inferInstanceAs (DecidableEq ((Γ ⊕ B) ⊕ (Endpoint arity label B ⊕
    Endpoint arity label' (PairBoundary arity label a b))))

private local instance : DecidableEq (Ambient arity label label' B Γ a b) := ambientDecidableEq

private local instance : FinEnum (RemainingCell a b) := subtypeEnum (fun c ↦ c ≠ a ∧ c ≠ b)

private def start (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    (rhs : PortNet arity label' (PairBoundary arity label a b)) :
    Wiring (Ambient arity label label' B Γ a b) × ℕ :=
  (w.sum (n.wiring.sum rhs.wiring), n.loops + rhs.loops)

private theorem contractFirst_spec (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    (h : n.Active a b) (rhs : PortNet arity label' (PairBoundary arity label a b)) :
    let s := Wiring.glue (boundaryPorts a b) (FinEnum.toList B)
      (Wiring.glue (pairPorts (active_ne h)) (FinEnum.toList _) (start n w rhs))
    Wiring.Respects (finalEmbedding (active_ne h)) ((n.contract h rhs).couple w).wiring s.1 ∧
      ((n.contract h rhs).couple w).loops = s.2 := by
  let s := Wiring.glue (pairPorts (active_ne h)) (FinEnum.toList _) (start n w rhs)
  have he : Wiring.Respects Function.Embedding.inr (n.wiring.sum rhs.wiring)
      (start n w rhs).1 := fun _ ↦ rfl
  have hc := n.contract_in h rhs Function.Embedding.inr (start n w rhs) he 0 (Nat.add_zero _)
  have hb : Wiring.Respects (afterContract (active_ne h))
      (w.sum (n.contract h rhs).wiring) s.1 := by
    rintro (p | p)
    · apply Wiring.glue_keeps
      · intro i bit; cases i <;> cases bit <;> intro h <;> cases h
      · intro i bit; cases i <;> cases bit <;> intro h <;> cases h
      · rfl
    · exact hc.1 p
  have ht := (n.contract h rhs).couple_in w (afterContract (active_ne h)) s hb 0 hc.2
  have hp : (couplePorts arity (Sum.elim (fun c : RemainingCell a b ↦ label c) label') Γ B).trans
      (afterContract (active_ne h)) = boundaryPorts a b := by
    ext p
    rcases p with ⟨p, bit⟩
    cases bit <;> rfl
  rw [hp] at ht
  have hf : (coupleEmbedding arity
      (Sum.elim (fun c : RemainingCell a b ↦ label c) label') Γ B).trans
        (afterContract (active_ne h)) = finalEmbedding (active_ne h) := by
    ext p
    rcases p with γ | ⟨c | d, p⟩ <;> rfl
  rw [hf] at ht
  exact ⟨ht.1, (Nat.add_zero _).symm.trans ht.2⟩

private theorem contextFirst_spec (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    (h : n.Active a b) (rhs : PortNet arity label' (PairBoundary arity label a b)) :
    let s := Wiring.glue (pairPorts (active_ne h)) (FinEnum.toList _)
      (Wiring.glue (boundaryPorts a b) (FinEnum.toList B) (start n w rhs))
    Wiring.Respects (finalEmbedding (active_ne h))
        ((n.couple w).contract (n.couple_active w h) rhs).wiring s.1 ∧
      ((n.couple w).contract (n.couple_active w h) rhs).loops = s.2 := by
  let s := Wiring.glue (boundaryPorts a b) (FinEnum.toList B) (start n w rhs)
  have he : Wiring.Respects (contextEmbedding a b) (w.sum n.wiring)
      (start n w rhs).1 := by rintro (p | p) <;> rfl
  have hc := n.couple_in w (contextEmbedding a b) (start n w rhs) he rhs.loops rfl
  have hb : Wiring.Respects (afterContext a b) ((n.couple w).wiring.sum rhs.wiring) s.1 := by
    rintro (p | p)
    · have hm (p : Endpoint arity label Γ) : afterContext (label' := label') a b (.inl p) =
          contextEmbedding a b (coupleEmbedding arity label Γ B p) := by cases p <;> rfl
      exact (congrArg s.1.partner (hm p)).trans
        ((hc.1 p).trans (hm ((n.couple w).wiring.partner p)).symm)
    · apply Wiring.glue_keeps
      · intro i bit; cases bit <;> intro h <;> cases h
      · intro i bit; cases bit <;> intro h <;> cases h
      · rfl
  have ht := (n.couple w).contract_in (n.couple_active w h) rhs (afterContext a b) s hb 0
    ((Nat.add_zero _).trans hc.2)
  have hp : (contractPorts arity label label' (active_ne (n.couple_active w h))).trans
      (afterContext (B := B) (Γ := Γ) a b) = pairPorts (active_ne h) := by
    ext p
    rcases p with ⟨i, bit⟩
    cases i <;> cases bit <;> rfl
  rw [hp] at ht
  exact ⟨ht.1, (Nat.add_zero _).symm.trans ht.2⟩

/-- Contracting an existing active pair commutes with attaching the surrounding boundary wires. -/
theorem contract_couple (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    (h : n.Active a b) (rhs : PortNet arity label' (PairBoundary arity label a b)) :
    let := subtypeEnum (fun c ↦ c ≠ a ∧ c ≠ b)
    (n.contract h rhs).couple w = (n.couple w).contract (n.couple_active w h) rhs := by
  have hc := contractFirst_spec n w h rhs
  have hb := contextFirst_spec n w h rhs
  have hg := Wiring.glue_glue (boundaryPorts a b) (pairPorts (active_ne h))
    (disjoint_ports (active_ne h)) (FinEnum.toList B) (FinEnum.toList _) (start n w rhs)
  rw [hg] at hb
  apply PortNet.ext
  · have hw := hc.1.map_eq hb.1 (Equiv.refl _) (fun _ ↦ rfl)
    simpa only [Wiring.map_refl] using hw
  · exact hc.2.trans hb.2.symm

end Geb.InteractionNet.PortNet

end
