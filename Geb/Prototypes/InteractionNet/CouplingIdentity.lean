/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphAssembly
public import Geb.Prototypes.InteractionNet.BoundaryRenaming
public import Geb.Prototypes.InteractionNet.WiringSubdivision
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Identity boundary attachment

Attaching one fresh wire at each boundary position simply moves the exposed endpoints.
Every processed position has a distinct new endpoint. No cell or existing closed wire is
changed, and these independent extensions create no new closed wire.

## Main definitions

* {lit}`Wiring.identityBoundary` — pair corresponding positions on two boundary copies.

## Main statements

* {lit}`PortNet.couple_identity` — identity boundary attachment leaves the net unchanged.

## Tags

interaction net, graph, boundary, identity, wire, attachment
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

/-- A separate wire joins each external position to the corresponding attachment position. -/
def Wiring.identityBoundary (B : Type) : Wiring (B ⊕ B) where
  partner := Sum.swap
  involutive p := by cases p <;> rfl
  fixedPointFree p h := by cases p <;> cases h

namespace PortNet

variable {α C B : Type} {arity : α → ℕ} {label : C → α}
variable [FinEnum C] [FinEnum B]

private def endpointDecidableEq : DecidableEq (Endpoint arity label B) :=
  let : DecidableEq C := FinEnum.decEq
  let : DecidableEq B := FinEnum.decEq
  inferInstanceAs (DecidableEq (B ⊕ (Σ c : C, Fin (arity (label c) + 1))))

private local instance : DecidableEq (Endpoint arity label B) := endpointDecidableEq

private def ambientDecidableEq : DecidableEq (CouplingEndpoint arity label B B) :=
  let : DecidableEq B := FinEnum.decEq
  let : DecidableEq (Endpoint arity label B) := endpointDecidableEq
  inferInstanceAs (DecidableEq ((B ⊕ B) ⊕ Endpoint arity label B))

private local instance : DecidableEq (CouplingEndpoint arity label B B) := ambientDecidableEq

private def extended (order : List B) : Endpoint arity label B ↪
    CouplingEndpoint arity label B B where
  toFun p := match p with
    | .inl b => if b ∈ order then .inl (.inl b) else .inr (.inl b)
    | .inr p => .inr (.inr p)
  inj' := by
    rintro (p | p) (q | q) h
    · by_cases hp : p ∈ order <;> by_cases hq : q ∈ order <;> simp_all
    · by_cases hp : p ∈ order <;> simp_all
    · by_cases hq : q ∈ order <;> simp_all
    · exact congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj h))

private def identityState (n : PortNet arity label B) (order : List B) :
    Wiring (CouplingEndpoint arity label B B) × ℕ :=
  Wiring.glue (couplePorts arity label B B) order
    ((Wiring.identityBoundary B).sum n.wiring, n.loops)

private theorem unused_wire (n : PortNet arity label B) (order : List B) (b : B)
    (hb : b ∉ order) :
    (identityState n order).1.partner (.inl (.inl b)) = .inl (.inr b) := by
  apply Wiring.glue_keeps_on
  · intro i _ bit
    cases bit <;> intro h <;> cases h
  · intro i hi bit
    cases bit with
    | false =>
      intro h
      exact hb ((Sum.inr.inj (Sum.inl.inj h)).symm ▸ hi)
    | true => intro h; cases h
  · rfl

private theorem identity_respects (n : PortNet arity label B) (order : List B)
    (unique : order.Nodup) :
    Wiring.Respects (extended order) n.wiring (identityState n order).1 := by
  refine List.reverseRecOn order (motive := fun order ↦ order.Nodup →
    Wiring.Respects (extended order) n.wiring (identityState n order).1)
      (fun _ ↦ ?_) (fun order b ih unique ↦ ?_) unique
  · have he : extended (arity := arity) (label := label) ([] : List B) =
        Function.Embedding.inr := by ext p; cases p <;> rfl
    rw [he]
    exact Wiring.respects_inr _ _
  · have hu := List.nodup_append.mp unique
    have hb : b ∉ order := fun h ↦ hu.2.2 b h b (List.mem_singleton_self b) rfl
    have he := ih hu.1
    let a : CouplingEndpoint arity label B B := .inl (.inl b)
    let cut : CouplingEndpoint arity label B B := .inl (.inr b)
    have hab : a ≠ cut := by simp [a, cut]
    have ha (p : Endpoint arity label B) : extended order p ≠ a := by
      rcases p with q | q
      · change (if q ∈ order then .inl (.inl q) else .inr (.inl q)) ≠ a
        by_cases hq : q ∈ order
        · simp only [hq, ↓reduceIte]
          intro h
          exact hb ((Sum.inl.inj (Sum.inl.inj h)) ▸ hq)
        · simp only [hq, ↓reduceIte]
          change (Sum.inr (Sum.inl q) : CouplingEndpoint arity label B B) ≠ .inl (.inl b)
          intro h
          cases h
      · change (Sum.inr (Sum.inr q) : CouplingEndpoint arity label B B) ≠ .inl (.inl b)
        intro h; cases h
    have hc (p : Endpoint arity label B) : extended order p ≠ cut := by
      rcases p with q | q
      · change (if q ∈ order then (.inl (.inl q) : CouplingEndpoint arity label B B)
          else .inr (.inl q)) ≠ .inl (.inr b)
        split_ifs <;> intro h <;> cases h
      · change (Sum.inr (Sum.inr q) : CouplingEndpoint arity label B B) ≠ .inl (.inr b)
        intro h; cases h
    have hs := he.shiftEndpoint (.inl b) a cut hab ha hc (unused_wire n order b hb)
    have hp : extended order (.inl b) = (.inr (.inl b) : CouplingEndpoint arity label B B) := by
      change (if b ∈ order then _ else _) = _
      simp only [hb, ↓reduceIte]
    rw [hp] at hs
    have heq : (Wiring.shiftEndpoint (.inl b)).trans
        (Wiring.adjoinWire (extended order) a cut hab ha hc) = extended (order ++ [b]) := by
      ext p
      rw [Wiring.adjoinWire_shift]
      rcases p with q | q
      · change (if (Sum.inl q : Endpoint arity label B) = .inl b then a else
          (if q ∈ order then .inl (.inl q) else .inr (.inl q))) =
            if q ∈ order ++ [b] then .inl (.inl q) else .inr (.inl q)
        by_cases hq : q = b <;> by_cases hm : q ∈ order <;> simp [a, hq, hm]
      · simp only [Sum.inr_ne_inl, ↓reduceIte]
        rfl
    rw [heq] at hs
    have hg : (identityState n (order ++ [b])).1 =
        (identityState n order).1.force cut (.inr (.inl b)) := by
      simp only [identityState, Wiring.glue, List.foldl_append, List.foldl_cons,
        List.foldl_nil, Wiring.glueAt]
      rfl
    rw [hg]
    exact hs

/-- Attaching the identity boundary matching preserves both the graph and its closed wires. -/
theorem couple_identity (n : PortNet arity label B) : n.couple (Wiring.identityBoundary B) = n := by
  have h := identity_respects n (FinEnum.toList B) FinEnum.nodup_toList
  have he : extended (arity := arity) (label := label) (FinEnum.toList B) =
      coupleEmbedding arity label B B := by
    ext p
    rcases p with b | p
    · change (if b ∈ FinEnum.toList B then _ else _) = _
      simp only [FinEnum.mem_toList, ↓reduceIte]
      rfl
    · rfl
  rw [he] at h
  have hs := n.couple_spec (Wiring.identityBoundary B)
  apply PortNet.ext
  · have hw := hs.1.map_eq h (Equiv.refl _) (fun _ ↦ rfl)
    simpa only [Wiring.map_refl] using hw
  · apply hs.2.trans
    apply Wiring.glue_loops_of_free_side _ _ FinEnum.nodup_toList _ false
    intro i _ j _ bit
    cases bit <;> intro h <;> cases h

/-- Attaching boundary wires along a bijection only renames the external boundary. -/
theorem couple_of_equiv {Δ : Type} [FinEnum Δ] (n : PortNet arity label B) (e : B ≃ Δ) :
    n.couple ((Wiring.identityBoundary B).map (Equiv.sumCongr e (Equiv.refl B))) =
      n.reboundary e := by
  rw [couple_reboundary, couple_identity]

end PortNet

end Geb.InteractionNet

end
