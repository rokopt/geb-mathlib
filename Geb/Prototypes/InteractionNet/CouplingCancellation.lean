/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.AssemblyEmbedding
public import Geb.Prototypes.InteractionNet.WiringCancellation
public import Geb.Prototypes.InteractionNet.WiringIndex
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Cancelling a wire component during boundary attachment

A separate wire contributes two boundary positions and no cells. Attaching both positions
to a surrounding matching joins their partners. The same graph is obtained by closing
those two positions in the surrounding matching first, retaining any resulting closed wire,
and attaching only the original graph's boundary.

## Main definitions

* {lit}`PortNet.adjoinWire` — add one disjoint boundary wire without allocating cells.

## Tags

interaction net, boundary, assembly, cancellation, closed wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

private local instance : FinEnum Bool := boolEnum

variable {α C B Γ : Type} {arity : α → ℕ} {label : C → α}

/-- Add a separate wire at two new boundary positions, retaining the original cells. -/
def adjoinWire (n : PortNet arity label B) : PortNet arity label (Bool ⊕ B) where
  wiring := (Wiring.wire.sum n.wiring).map (Equiv.sumAssoc Bool B (CellPort arity label)).symm
  loops := n.loops

/-- Put a context's distinguished endpoints beside its other attachment positions. -/
def wireBoundaryEquiv (Γ B : Type) : Bool ⊕ (Γ ⊕ B) ≃ Γ ⊕ (Bool ⊕ B) where
  toFun p := match p with
    | .inl b => .inr (.inl b)
    | .inr (.inl γ) => .inl γ
    | .inr (.inr b) => .inr (.inr b)
  invFun p := match p with
    | .inl γ => .inr (.inl γ)
    | .inr (.inl b) => .inl b
    | .inr (.inr b) => .inr (.inr b)
  left_inv p := by rcases p with b | (γ | b) <;> rfl
  right_inv p := by rcases p with γ | (b | b) <;> rfl

private abbrev Ambient (arity : α → ℕ) (label : C → α) (Γ B : Type) :=
  Bool ⊕ (Bool ⊕ ((Γ ⊕ B) ⊕ Endpoint arity label B))

private def ambientEquiv : Ambient arity label Γ B ≃
    CouplingEndpoint arity label Γ (Bool ⊕ B) where
  toFun p := match p with
    | .inl b => .inr (.inl (.inl b))
    | .inr (.inl b) => .inl (.inr (.inl b))
    | .inr (.inr (.inl (.inl γ))) => .inl (.inl γ)
    | .inr (.inr (.inl (.inr b))) => .inl (.inr (.inr b))
    | .inr (.inr (.inr (.inl b))) => .inr (.inl (.inr b))
    | .inr (.inr (.inr (.inr p))) => .inr (.inr p)
  invFun p := match p with
    | .inl (.inl γ) => .inr (.inr (.inl (.inl γ)))
    | .inl (.inr (.inl b)) => .inr (.inl b)
    | .inl (.inr (.inr b)) => .inr (.inr (.inl (.inr b)))
    | .inr (.inl (.inl b)) => .inl b
    | .inr (.inl (.inr b)) => .inr (.inr (.inr (.inl b)))
    | .inr (.inr p) => .inr (.inr (.inr (.inr p)))
  left_inv p := by rcases p with b | (b | ((γ | b) | (b | p))) <;> rfl
  right_inv p := by rcases p with (γ | (b | b)) | ((b | b) | p) <;> rfl

private def start (n : PortNet arity label B) (w : Wiring (Bool ⊕ (Γ ⊕ B))) :
    Wiring (Ambient arity label Γ B) × ℕ :=
  (Wiring.wire.sum ((w.sum n.wiring).map (Equiv.sumAssoc Bool (Γ ⊕ B) _)), n.loops)

private theorem start_wiring (n : PortNet arity label B) (w : Wiring (Bool ⊕ (Γ ⊕ B))) :
    (start n w).1.map ambientEquiv =
      (w.map (wireBoundaryEquiv Γ B)).sum n.adjoinWire.wiring := by
  apply Wiring.ext
  funext p
  rcases p with (γ | (b | b)) | ((b | b) | p)
  all_goals dsimp [start, Wiring.map, Wiring.sum, ambientEquiv, adjoinWire,
    wireBoundaryEquiv, Equiv.sumAssoc]
  · cases hw : w.partner (.inr (.inl γ)) with
    | inl b => simp_all
    | inr q => cases q <;> simp_all
  · cases hw : w.partner (.inl b) with
    | inl b => simp_all
    | inr q => cases q <;> simp_all
  · cases hw : w.partner (.inr (.inr b)) with
    | inl b => simp_all
    | inr q => cases q <;> simp_all
  · cases hn : n.wiring.partner (.inl b) <;> rfl
  · cases hn : n.wiring.partner (.inr p) <;> rfl

variable [FinEnum C] [FinEnum B] [FinEnum Γ]

private def endpointDecidableEq : DecidableEq (Endpoint arity label B) :=
  let : DecidableEq C := FinEnum.decEq
  let : DecidableEq B := FinEnum.decEq
  inferInstanceAs (DecidableEq (B ⊕ (Σ c : C, Fin (arity (label c) + 1))))

private local instance : DecidableEq (Endpoint arity label B) := endpointDecidableEq

private def ambientDecidableEq : DecidableEq (Ambient arity label Γ B) :=
  let : DecidableEq (Endpoint arity label B) := endpointDecidableEq
  inferInstanceAs (DecidableEq (Bool ⊕ (Bool ⊕ ((Γ ⊕ B) ⊕ Endpoint arity label B))))

private local instance : DecidableEq (Ambient arity label Γ B) := ambientDecidableEq

private def remainingEmbedding : CouplingEndpoint arity label Γ B ↪ Ambient arity label Γ B :=
  Function.Embedding.inr.trans .inr

private def finalEmbedding : Endpoint arity label Γ ↪ Ambient arity label Γ B :=
  (coupleEmbedding arity label Γ B).trans remainingEmbedding

private def remainingPorts : B × Bool ↪ Ambient arity label Γ B :=
  (couplePorts arity label Γ B).trans remainingEmbedding

private def cancelled (n : PortNet arity label B) (w : Wiring (Bool ⊕ (Γ ⊕ B))) :
    Wiring (Ambient arity label Γ B) × ℕ :=
  Wiring.glue (Wiring.closeWirePorts _) [true, false] (start n w)

private theorem cancelled_spec (n : PortNet arity label B) (w : Wiring (Bool ⊕ (Γ ⊕ B))) :
    Wiring.Respects remainingEmbedding ((Wiring.closeWire w).1.sum n.wiring)
      (cancelled n w).1 ∧ (cancelled n w).2 = n.loops + (Wiring.closeWire w).2 := by
  have h := Wiring.closeWire_subdivision
    ((w.sum n.wiring).map (Equiv.sumAssoc Bool (Γ ⊕ B) _)) n.loops
  rw [Wiring.closeWire_sum] at h
  exact h

private theorem reduced_spec (n : PortNet arity label B) (w : Wiring (Bool ⊕ (Γ ⊕ B))) :
    let s := Wiring.glue remainingPorts (FinEnum.toList B) (cancelled n w)
    Wiring.Respects finalEmbedding (n.couple (Wiring.closeWire w).1).wiring s.1 ∧
      (n.couple (Wiring.closeWire w).1).loops + (Wiring.closeWire w).2 = s.2 := by
  have hc := cancelled_spec n w
  exact n.couple_in (Wiring.closeWire w).1 remainingEmbedding (cancelled n w) hc.1
    (Wiring.closeWire w).2 hc.2.symm

private theorem original_spec (n : PortNet arity label B) (w : Wiring (Bool ⊕ (Γ ⊕ B))) :
    let s := Wiring.glue remainingPorts (FinEnum.toList B) (cancelled n w)
    Wiring.Respects finalEmbedding
      (n.adjoinWire.couple (w.map (wireBoundaryEquiv Γ B))).wiring s.1 ∧
      (n.adjoinWire.couple (w.map (wireBoundaryEquiv Γ B))).loops = s.2 := by
  let ports := (couplePorts arity label Γ (Bool ⊕ B)).trans ambientEquiv.symm.toEmbedding
  have he := Wiring.respects_map_symm ambientEquiv (start n w).1
  rw [start_wiring] at he
  have h := n.adjoinWire.couple_in (w.map (wireBoundaryEquiv Γ B))
    ambientEquiv.symm.toEmbedding (start n w) he 0 (Nat.add_zero _)
  have hf : (coupleEmbedding arity label Γ (Bool ⊕ B)).trans
      ambientEquiv.symm.toEmbedding = (finalEmbedding : Endpoint arity label Γ ↪ _) := by
    ext p
    cases p <;> rfl
  rw [hf] at h
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
  have hbool (s : Wiring (Ambient arity label Γ B) × ℕ) (b : Bool) :
      Wiring.glueAt ports s (.inl b) = Wiring.glueAt (Wiring.closeWirePorts _) s b := by
    apply Prod.ext
    · exact Wiring.force_comm s.1 (by intro h; cases h)
    · exact congrArg (s.2 + ·) (Wiring.loopDelta_comm s.1 _ _)
  have hrest (s : Wiring (Ambient arity label Γ B) × ℕ) (b : B) :
      Wiring.glueAt ports s (.inr b) = Wiring.glueAt remainingPorts s b := rfl
  have hg : Wiring.glue ports (FinEnum.toList (Bool ⊕ B)) (start n w) =
      Wiring.glue remainingPorts (FinEnum.toList B) (cancelled n w) := by
    rw [Wiring.glue_perm ports order]
    simp only [Wiring.glue, List.foldl_cons, List.foldl_map, hbool, hrest]
    rfl
  change Wiring.Respects finalEmbedding _ (Wiring.glue ports _ (start n w)).1 ∧
    _ + 0 = (Wiring.glue ports _ (start n w)).2 at h
  rw [hg, Nat.add_zero] at h
  exact h

/-- A disjoint wire can be cancelled in the boundary context, retaining its closed component. -/
theorem couple_adjoinWire (n : PortNet arity label B) (w : Wiring (Bool ⊕ (Γ ⊕ B))) :
    let := boolEnum
    n.adjoinWire.couple (w.map (wireBoundaryEquiv Γ B)) =
      { n.couple (Wiring.closeWire w).1 with
        loops := (n.couple (Wiring.closeWire w).1).loops + (Wiring.closeWire w).2 } := by
  have hs := original_spec n w
  have hr := reduced_spec n w
  apply PortNet.ext
  · have h := hs.1.map_eq hr.1 (Equiv.refl _) (fun _ ↦ rfl)
    simpa only [Wiring.map_refl] using h
  · exact hs.2.trans hr.2.symm

end Geb.InteractionNet.PortNet

end
