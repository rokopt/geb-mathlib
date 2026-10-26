/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.AssemblyEmbedding
public import Geb.Prototypes.InteractionNet.WiringCompose
public import Geb.Prototypes.InteractionNet.BoundaryComposition
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Successive boundary attachments compose

Attaching an inner matching and then an outer matching agrees with first composing those
matchings and attaching the result. Both executions allocate the same endpoints. Their two
families of wire splices have disjoint endpoints, so gluing commutation identifies the final
matching and the total number of closed wires.

## Main statements

* {lit}`PortNet.couple_couple` — successive boundary attachments equal attachment of their
  composite, including the composite's closed-wire count.

## Tags

interaction net, graph, boundary, assembly, composition, closed wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

variable {α C B Γ Δ : Type} {arity : α → ℕ} {label : C → α}

private abbrev Ambient (arity : α → ℕ) (label : C → α) (B Γ Δ : Type) :=
  ((Γ ⊕ B) ⊕ (Δ ⊕ Γ)) ⊕ Endpoint arity label B

private def innerEmbedding : CouplingEndpoint arity label Γ B ↪ Ambient arity label B Γ Δ :=
  Function.Embedding.sumMap .inl (.refl _)

private def outerEmbedding : CouplingEndpoint arity label Δ Γ ↪ Ambient arity label B Γ Δ where
  toFun p := match p with
    | .inl p => .inl (.inr p)
    | .inr (.inl p) => .inl (.inl (.inl p))
    | .inr (.inr p) => .inr (.inr p)
  inj' := by
    rintro (p | (p | p)) (q | (q | q)) h <;> simp_all

private def finalEmbedding : Endpoint arity label Δ ↪ Ambient arity label B Γ Δ where
  toFun p := match p with
    | .inl p => .inl (.inr (.inl p))
    | .inr p => .inr (.inr p)
  inj' := by
    rintro (p | p) (q | q) h <;> simp_all

private def innerPorts : B × Bool ↪ Ambient arity label B Γ Δ :=
  (couplePorts arity label Γ B).trans innerEmbedding

private def sharedPorts : Γ × Bool ↪ Ambient arity label B Γ Δ :=
  (Wiring.composeBoundaryPorts B Γ Δ).trans .inl

private theorem disjoint_ports (i : B) (a : Bool) (j : Γ) (b : Bool) :
    innerPorts (arity := arity) (label := label) (Δ := Δ) (i, a) ≠ sharedPorts (j, b) := by
  cases a <;> cases b <;> intro h <;> cases h

variable [FinEnum C] [FinEnum B] [FinEnum Γ] [FinEnum Δ]

private def endpointDecidableEq : DecidableEq (Endpoint arity label B) :=
  let : DecidableEq C := FinEnum.decEq
  let : DecidableEq B := FinEnum.decEq
  inferInstanceAs (DecidableEq (B ⊕ (Σ c : C, Fin (arity (label c) + 1))))

private local instance : DecidableEq (Endpoint arity label B) := endpointDecidableEq

private def ambientDecidableEq : DecidableEq (Ambient arity label B Γ Δ) :=
  @instDecidableEqSum ((Γ ⊕ B) ⊕ (Δ ⊕ Γ)) (Endpoint arity label B)
    inferInstance endpointDecidableEq

private local instance : DecidableEq (Ambient arity label B Γ Δ) := ambientDecidableEq

private def start (n : PortNet arity label B) (w : Wiring (Γ ⊕ B)) (v : Wiring (Δ ⊕ Γ)) :
    Wiring (Ambient arity label B Γ Δ) × ℕ := ((w.sum v).sum n.wiring, n.loops)

private theorem successive_spec (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    (v : Wiring (Δ ⊕ Γ)) :
    let s := Wiring.glue sharedPorts (FinEnum.toList Γ)
      (Wiring.glue innerPorts (FinEnum.toList B) (start n w v))
    Wiring.Respects finalEmbedding ((n.couple w).couple v).wiring s.1 ∧
      ((n.couple w).couple v).loops = s.2 := by
  let s := Wiring.glue innerPorts (FinEnum.toList B) (start n w v)
  have he : Wiring.Respects innerEmbedding (w.sum n.wiring) (start n w v).1 := by
    rintro (p | p) <;> rfl
  have hi := n.couple_in w innerEmbedding (start n w v) he 0 (Nat.add_zero _)
  have ho : Wiring.Respects outerEmbedding (v.sum (n.couple w).wiring) s.1 := by
    rintro (p | p)
    · apply Wiring.glue_keeps
      · intro i bit; cases bit <;> intro h <;> cases h
      · intro i bit; cases bit <;> intro h <;> cases h
      · rfl
    · have hm (p : Endpoint arity label Γ) : outerEmbedding (Δ := Δ) (.inr p) =
          innerEmbedding (coupleEmbedding arity label Γ B p) := by cases p <;> rfl
      exact (congrArg s.1.partner (hm p)).trans
        ((hi.1 p).trans (hm ((n.couple w).wiring.partner p)).symm)
  have hl : (n.couple w).loops + 0 = s.2 := hi.2
  have ht := (n.couple w).couple_in v outerEmbedding s ho 0 hl
  have hp : (couplePorts arity label Δ Γ).trans outerEmbedding =
      (sharedPorts : Γ × Bool ↪ Ambient arity label B Γ Δ) := by
    ext p
    rcases p with ⟨p, bit⟩
    cases bit <;> rfl
  rw [hp] at ht
  have hf : (coupleEmbedding arity label Δ Γ).trans outerEmbedding =
      (finalEmbedding : Endpoint arity label Δ ↪ Ambient arity label B Γ Δ) := by
    ext p
    cases p <;> rfl
  rw [hf] at ht
  constructor
  · exact ht.1
  · simpa only [Nat.add_zero] using ht.2

private def compositeEmbedding : CouplingEndpoint arity label Δ B ↪ Ambient arity label B Γ Δ :=
  (Wiring.composeBoundaryEmbedding B Γ Δ).sumMap (.refl _)

private theorem composite_spec (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    (v : Wiring (Δ ⊕ Γ)) :
    let s := Wiring.glue innerPorts (FinEnum.toList B)
      (Wiring.glue sharedPorts (FinEnum.toList Γ) (start n w v))
    Wiring.Respects finalEmbedding (n.couple (Wiring.composeBoundary w v).1).wiring s.1 ∧
      (n.couple (Wiring.composeBoundary w v).1).loops + (Wiring.composeBoundary w v).2 = s.2 := by
  let s := Wiring.glue sharedPorts (FinEnum.toList Γ) (start n w v)
  have hc := Wiring.composeBoundary_spec w v
  have hg := Wiring.glue_sum_left (Wiring.composeBoundaryPorts B Γ Δ) (FinEnum.toList Γ)
    (w.sum v, 0) n.wiring n.loops
  simp only [Nat.zero_add] at hg
  have hgs : s =
      ((Wiring.glue (Wiring.composeBoundaryPorts B Γ Δ) (FinEnum.toList Γ) (w.sum v, 0)).1.sum
        n.wiring,
        (Wiring.glue (Wiring.composeBoundaryPorts B Γ Δ) (FinEnum.toList Γ) (w.sum v, 0)).2 +
          n.loops) := hg
  have he : Wiring.Respects compositeEmbedding
      ((Wiring.composeBoundary w v).1.sum n.wiring) s.1 := by
    rw [hgs]
    exact hc.1.sum (Wiring.respects_refl n.wiring)
  have hl : n.loops + (Wiring.composeBoundary w v).2 = s.2 := by
    rw [hgs, hc.2, Nat.add_comm]
  have ht := n.couple_in (Wiring.composeBoundary w v).1 compositeEmbedding s he
    (Wiring.composeBoundary w v).2 hl
  have hp : (couplePorts arity label Δ B).trans compositeEmbedding =
      (innerPorts : B × Bool ↪ Ambient arity label B Γ Δ) := by
    ext p
    rcases p with ⟨p, bit⟩
    cases bit <;> rfl
  rw [hp] at ht
  have hf : (coupleEmbedding arity label Δ B).trans compositeEmbedding =
      (finalEmbedding : Endpoint arity label Δ ↪ Ambient arity label B Γ Δ) := by
    ext p
    cases p <;> rfl
  rw [hf] at ht
  constructor
  · exact ht.1
  · exact ht.2

/-- Attaching two matchings equals attaching their composite and retaining its closed wires. -/
theorem couple_couple (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    (v : Wiring (Δ ⊕ Γ)) :
    (n.couple w).couple v =
      { n.couple (Wiring.composeBoundary w v).1 with
        loops := (n.couple (Wiring.composeBoundary w v).1).loops +
          (Wiring.composeBoundary w v).2 } := by
  have hs := successive_spec n w v
  have hc := composite_spec n w v
  have hg := Wiring.glue_glue
    (innerPorts : B × Bool ↪ Ambient arity label B Γ Δ) sharedPorts
    disjoint_ports (FinEnum.toList B) (FinEnum.toList Γ) (start n w v)
  rw [← hg] at hc
  apply PortNet.ext
  · have hw := hs.1.map_eq hc.1 (Equiv.refl _) (fun _ ↦ rfl)
    simpa only [Wiring.map_refl] using hw
  · exact hs.2.trans hc.2.symm

end Geb.InteractionNet.PortNet

end
