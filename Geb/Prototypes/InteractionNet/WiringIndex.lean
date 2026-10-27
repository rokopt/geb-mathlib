/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.WiringGlue
public import Mathlib.Data.FinEnum
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Reindexing a family of wire splices

Renaming the indices of a finite family of disjoint splices changes neither its wires
nor its closed-wire count. The proof compares the two explicit enumerations as lists.

## Main statements

* {lit}`Wiring.glue_index` — reindexing cuts agrees with mapping the execution order.
* {lit}`Wiring.glue_enum_equiv` — complete gluing is independent of its finite index type.

## Tags

interaction net, gluing, enumeration, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

open scoped FinEnum

variable {I J P : Type*} [DecidableEq P]

/-- Reindexing the cuts has the same effect as mapping their execution order. -/
theorem glue_index (e : I ≃ J) (ports : J × Bool ↪ P) (order : List I)
    (s : Wiring P × ℕ) :
    glue ((e.prodCongr (Equiv.refl Bool)).toEmbedding.trans ports) order s =
      glue ports (order.map e) s := by
  unfold glue
  rw [List.foldl_map]
  rfl

/-- Move a selected occurrence to the head, constructively removing it from the remainder. -/
theorem perm_cons_erase [DecidableEq J] (a : J) (xs : List J) (h : a ∈ xs) :
    xs.Perm (a :: xs.erase a) := by
  revert h
  refine List.rec (fun h ↦ (List.not_mem_nil h).elim) ?_ xs
  intro b bs ih h
  by_cases he : b = a
  · subst b
    simpa only [List.erase_cons_head] using (List.Perm.refl (a :: bs))
  · have hm : a ∈ bs := (List.mem_cons.mp h).resolve_left (Ne.symm he)
    rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using he)]
    exact (List.Perm.cons b (ih hm)).trans (List.Perm.swap _ _ _)

private theorem perm_of_count [DecidableEq J] (xs ys : List J)
    (h : ∀ j, xs.count j = ys.count j) : xs.Perm ys := by
  revert ys
  refine List.rec ?_ ?_ xs
  · intro ys h
    cases ys with
    | nil => exact List.Perm.nil
    | cons a ys =>
      have ha := h a
      simp only [List.count_nil, List.count_cons_self] at ha
      exact (Nat.noConfusion ha)
  · intro a xs ih ys h
    have ha : a ∈ ys := List.count_pos_iff.mp (by rw [← h]; simp)
    apply (List.Perm.cons a (ih (ys.erase a) ?_)).trans (perm_cons_erase a ys ha).symm
    intro j
    have hj := h j
    rw [(perm_cons_erase a ys ha).count_eq] at hj
    simp only [List.count_cons] at hj
    exact Nat.add_right_cancel hj

/-- A bijection maps one duplicate-free exhaustive enumeration to another, up to order. -/
theorem enum_perm [FinEnum I] [FinEnum J] (e : I ≃ J) :
    ((FinEnum.toList I).map e).Perm (FinEnum.toList J) := by
  apply perm_of_count
  intro j
  rw [(List.Nodup.map e.injective FinEnum.nodup_toList).count, FinEnum.nodup_toList.count]
  have hm : j ∈ (FinEnum.toList I).map e :=
    List.mem_map.mpr ⟨e.symm j, FinEnum.mem_toList _, e.apply_symm_apply j⟩
  simp only [hm, FinEnum.mem_toList, ↓reduceIte]

/-- Complete gluing does not depend on the chosen finite index type. -/
theorem glue_enum_equiv [FinEnum I] [FinEnum J] (e : I ≃ J) (ports : J × Bool ↪ P)
    (s : Wiring P × ℕ) :
    glue ((e.prodCongr (Equiv.refl Bool)).toEmbedding.trans ports) (FinEnum.toList I) s =
      glue ports (FinEnum.toList J) s := by
  rw [glue_index]
  exact glue_perm ports (enum_perm e) s

end Geb.InteractionNet.Wiring

end
