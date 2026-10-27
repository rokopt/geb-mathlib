/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.BoundaryClosure
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# A boundary splice as boundary attachment

Joining two boundary positions removes them, connects their former partners and records
any closed wire. Attaching the pair-closing boundary matching performs exactly this splice
while retaining every other boundary position and cell.

## Main definitions

* {lit}`PortNet.closeBoundaryPair` — splice a distinguished pair of boundary positions.

## Tags

interaction net, boundary, splice, assembly, closed wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

variable {α C B : Type} {arity : α → ℕ} {label : C → α}
variable [FinEnum C] [FinEnum B]

private local instance : FinEnum Bool := boolEnum

private def endpointDecidableEq : DecidableEq (Endpoint arity label B) :=
  let : DecidableEq C := FinEnum.decEq
  let : DecidableEq B := FinEnum.decEq
  inferInstanceAs (DecidableEq (B ⊕ (Σ c : C, Fin (arity (label c) + 1))))

private local instance : DecidableEq (Endpoint arity label B) := endpointDecidableEq

/-- Join and remove the two distinguished boundary positions, retaining cells and closed wires. -/
def closeBoundaryPair (n : PortNet arity label (Bool ⊕ B)) : PortNet arity label B :=
  let : DecidableEq C := FinEnum.decEq
  let : DecidableEq B := FinEnum.decEq
  let : DecidableEq (Endpoint arity label B) :=
    inferInstanceAs (DecidableEq (B ⊕ (Σ c : C, Fin (arity (label c) + 1))))
  let s := Wiring.closeWire (n.wiring.map (Equiv.sumAssoc Bool B (CellPort arity label)))
  ⟨s.1, n.loops + s.2⟩

/-- The closed net retains the other boundary positions and every cell port in the splice. -/
theorem closeBoundaryPair_spec (n : PortNet arity label (Bool ⊕ B)) :
    let := boolEnum
    let : DecidableEq (Endpoint arity label (Bool ⊕ B)) :=
      let : DecidableEq C := FinEnum.decEq
      let : DecidableEq B := FinEnum.decEq
      inferInstanceAs (DecidableEq ((Bool ⊕ B) ⊕ (Σ c : C, Fin (arity (label c) + 1))))
    Wiring.Respects (Function.Embedding.sumMap .inr (.refl _)) n.closeBoundaryPair.wiring
      (n.wiring.force (.inl (.inl false)) (.inl (.inl true))) := by
  let := boolEnum
  let : DecidableEq (Endpoint arity label (Bool ⊕ B)) :=
    let : DecidableEq C := FinEnum.decEq
    let : DecidableEq B := FinEnum.decEq
    inferInstanceAs (DecidableEq ((Bool ⊕ B) ⊕ (Σ c : C, Fin (arity (label c) + 1))))
  let e := Equiv.sumAssoc Bool B (CellPort arity label)
  have h := Wiring.closeWire_respects (n.wiring.map e)
  have hm := Wiring.force_map e n.wiring
    (a := .inl (.inl false)) (b := .inl (.inl true)) (by intro h; cases h)
  erw [← hm] at h
  have hs := h.trans (Wiring.respects_map_symm e _)
  exact hs

/-- Closing a boundary pair adds one closed wire precisely when its ends were already joined. -/
theorem closeBoundaryPair_loops (n : PortNet arity label (Bool ⊕ B)) :
    let := boolEnum
    let : DecidableEq (Endpoint arity label (Bool ⊕ B)) :=
      let : DecidableEq C := FinEnum.decEq
      let : DecidableEq B := FinEnum.decEq
      inferInstanceAs (DecidableEq ((Bool ⊕ B) ⊕ (Σ c : C, Fin (arity (label c) + 1))))
    n.closeBoundaryPair.loops = n.loops +
      n.wiring.loopDelta (.inl (.inl false)) (.inl (.inl true)) := by
  let := boolEnum
  let : DecidableEq (Endpoint arity label (Bool ⊕ B)) :=
    let : DecidableEq C := FinEnum.decEq
    let : DecidableEq B := FinEnum.decEq
    inferInstanceAs (DecidableEq ((Bool ⊕ B) ⊕ (Σ c : C, Fin (arity (label c) + 1))))
  exact congrArg (n.loops + ·) (Wiring.loopDelta_map
    (Equiv.sumAssoc Bool B (CellPort arity label)) n.wiring
      (.inl (.inl false)) (.inl (.inl true)))

private abbrev Ambient (arity : α → ℕ) (label : C → α) (B : Type) :=
  CouplingEndpoint arity label B (Bool ⊕ B)

private def ambientDecidableEq : DecidableEq (Ambient arity label B) :=
  let : DecidableEq C := FinEnum.decEq
  let : DecidableEq B := FinEnum.decEq
  inferInstanceAs (DecidableEq ((B ⊕ (Bool ⊕ B)) ⊕ ((Bool ⊕ B) ⊕
    (Σ c : C, Fin (arity (label c) + 1)))))

private local instance : DecidableEq (Ambient arity label B) := ambientDecidableEq

private def wireEmbedding : Bool ⊕ (Bool ⊕ Endpoint arity label B) ↪ Ambient arity label B :=
  Function.Embedding.sumMap (Function.Embedding.inl.trans .inr)
    (Equiv.sumAssoc Bool B (CellPort arity label)).symm.toEmbedding

private def remainingEmbedding : CouplingEndpoint arity label B B ↪ Ambient arity label B :=
  Function.Embedding.sumMap
    (Function.Embedding.sumMap (.refl B) .inr)
    (Function.Embedding.sumMap .inr (.refl _))

private def wirePorts : Bool × Bool ↪ Ambient arity label B :=
  (Wiring.closeWirePorts (Endpoint arity label B)).trans wireEmbedding

private def start (n : PortNet arity label (Bool ⊕ B)) : Wiring (Ambient arity label B) × ℕ :=
  ((Wiring.closePairBoundary B).sum n.wiring, n.loops)

private def cancelled (n : PortNet arity label (Bool ⊕ B)) : Wiring (Ambient arity label B) × ℕ :=
  Wiring.glue wirePorts [true, false] (start n)

omit [FinEnum C] [FinEnum B] in
private theorem wire_respects (n : PortNet arity label (Bool ⊕ B)) :
    Wiring.Respects wireEmbedding
      (Wiring.wire.sum (n.wiring.map (Equiv.sumAssoc Bool B (CellPort arity label))))
      (start n).1 := by
  have hn : Wiring.Respects
      ((Equiv.sumAssoc Bool B (CellPort arity label)).symm.toEmbedding.trans
        Function.Embedding.inr)
      (n.wiring.map (Equiv.sumAssoc Bool B (CellPort arity label))) (start n).1 := by
    exact (Wiring.respects_map_symm (Equiv.sumAssoc Bool B (CellPort arity label)) n.wiring).trans
      (Wiring.respects_inr _ n.wiring)
  rintro (b | p)
  · cases b <;> rfl
  · exact hn p

private theorem cancelled_spec (n : PortNet arity label (Bool ⊕ B)) :
    Wiring.Respects remainingEmbedding
      ((Wiring.identityBoundary B).sum n.closeBoundaryPair.wiring) (cancelled n).1 ∧
      n.closeBoundaryPair.loops = (cancelled n).2 := by
  let w := n.wiring.map (Equiv.sumAssoc Bool B (CellPort arity label))
  have hc := Wiring.closeWire_subdivision w n.loops
  have hg := (wire_respects n).glue (Wiring.closeWirePorts _) [true, false]
    (Wiring.wire.sum w, n.loops) (start n) rfl
  have hn := hc.1.trans hg.1
  constructor
  · rintro (p | p)
    · apply Wiring.glue_keeps
      · intro i b
        cases b <;> cases p <;> intro h <;> cases h
      · intro i b
        cases b <;> cases p <;> intro h <;> cases h
      · cases p <;> rfl
    · exact hn p
  · exact hc.2.symm.trans hg.2

private def remainingPorts : B × Bool ↪ Ambient arity label B :=
  (couplePorts arity label B B).trans remainingEmbedding

private def finalEmbedding : Endpoint arity label B ↪ Ambient arity label B :=
  (coupleEmbedding arity label B B).trans remainingEmbedding

private theorem reduced_spec (n : PortNet arity label (Bool ⊕ B)) :
    let s := Wiring.glue remainingPorts (FinEnum.toList B) (cancelled n)
    Wiring.Respects finalEmbedding n.closeBoundaryPair.wiring s.1 ∧
      n.closeBoundaryPair.loops = s.2 := by
  have hc := cancelled_spec n
  have h := n.closeBoundaryPair.couple_in (Wiring.identityBoundary B)
    remainingEmbedding (cancelled n) hc.1 0 (by simpa only [Nat.add_zero] using hc.2)
  rw [couple_identity, Nat.add_zero] at h
  exact h

private theorem original_spec (n : PortNet arity label (Bool ⊕ B)) :
    let s := Wiring.glue remainingPorts (FinEnum.toList B) (cancelled n)
    Wiring.Respects finalEmbedding (n.couple (Wiring.closePairBoundary B)).wiring s.1 ∧
      (n.couple (Wiring.closePairBoundary B)).loops = s.2 := by
  let ports := couplePorts arity label B (Bool ⊕ B)
  have h := n.couple_spec (Wiring.closePairBoundary B)
  have order : (FinEnum.toList (Bool ⊕ B)).Perm
      (.inl true :: .inl false :: (FinEnum.toList B).map Sum.inr) := by
    apply Wiring.enum_perm_of_cover
    · simp only [List.nodup_cons, List.mem_cons, Sum.inl.injEq,
        List.mem_map, Sum.inr_ne_inl, and_false, exists_false, or_false, not_false_eq_true,
        true_and]
      exact ⟨by decide, FinEnum.nodup_toList.map Sum.inr_injective⟩
    · rintro (b | b)
      · cases b <;> simp
      · simp only [List.mem_cons, Sum.inr_ne_inl, false_or, List.mem_map]
        exact ⟨b, FinEnum.mem_toList b, rfl⟩
  have hbool (s : Wiring (Ambient arity label B) × ℕ) (b : Bool) :
      Wiring.glueAt ports s (.inl b) = Wiring.glueAt wirePorts s b := rfl
  have hrest (s : Wiring (Ambient arity label B) × ℕ) (b : B) :
      Wiring.glueAt ports s (.inr b) = Wiring.glueAt remainingPorts s b := rfl
  have hg : Wiring.glue ports (FinEnum.toList (Bool ⊕ B)) (start n) =
      Wiring.glue remainingPorts (FinEnum.toList B) (cancelled n) := by
    rw [Wiring.glue_perm ports order]
    simp only [Wiring.glue, List.foldl_cons, List.foldl_map, hbool, hrest]
    rfl
  have hf : coupleEmbedding arity label B (Bool ⊕ B) =
      (finalEmbedding : Endpoint arity label B ↪ _) := by
    ext p
    cases p <;> rfl
  change Wiring.Respects (coupleEmbedding arity label B (Bool ⊕ B)) _
    (Wiring.glue ports _ (start n)).1 ∧ _ = (Wiring.glue ports _ (start n)).2 at h
  rw [hf, hg] at h
  exact h

/-- Closing two boundary positions directly agrees with attaching a wire between them. -/
theorem couple_closePair_eq (n : PortNet arity label (Bool ⊕ B)) :
    let := boolEnum
    n.couple (Wiring.closePairBoundary B) = n.closeBoundaryPair := by
  have hs := original_spec n
  have hr := reduced_spec n
  apply PortNet.ext
  · have h := hs.1.map_eq hr.1 (Equiv.refl _) (fun _ ↦ rfl)
    simpa only [Wiring.map_refl] using h
  · exact hs.2.trans hr.2.symm

end Geb.InteractionNet.PortNet

end
