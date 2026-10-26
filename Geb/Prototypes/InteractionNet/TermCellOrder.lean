/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermGraph
public import Geb.Prototypes.InteractionNet.GraphReadback
import Geb.Cslib.Foundations.Data.PFunctor.Free
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Visiting every cell of a term graph

Constructor traversal visits the parent before its children, following their auxiliary
ports in order. This syntax order enumerates every graph cell exactly once. Its length
therefore agrees with the compiler's finite cell count, independently of the runtime's
choice of ordinal indices.

## Main definitions

* {lit}`Term.cellOrder` — the parent-first traversal order of a term's cells.

## Main statements

* {lit}`Term.cellOrder_unique` — traversal never repeats a cell.
* {lit}`Term.cellOrder_cover` — traversal contains every cell.
* {lit}`Term.cellOrder_length` — traversal length equals the finite cell count.

## Tags

interaction net, term, graph, cell, enumeration, traversal
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Term

open scoped FinEnum

variable {α ν : Type} {arity : α → ℕ}

/-- Visit the parent before the ordered families of cells in its children. -/
def cellOrder (t : Term arity ν) : List t.fragment.Cell :=
  PFunctor.FreeM.rec (fun _ ↦ []) (fun a ts orders ↦
    Sum.inl () :: (List.finRange (arity a)).flatMap
      (fun i ↦ (orders i).map (fun c ↦ Sum.inr (⟨i, c⟩ : Σ i, (fragment (ts i)).Cell)))) t

/-- The parent-first syntax order does not visit any cell twice. -/
theorem cellOrder_unique (t : Term arity ν) : t.cellOrder.Nodup := by
  refine PFunctor.FreeM.rec (fun _ ↦ List.nodup_nil) (fun a ts ih ↦ ?_) t
  change (Sum.inl () :: (List.finRange (arity a)).flatMap
    (fun i ↦ (cellOrder (ts i)).map
      (fun c ↦ Sum.inr (⟨i, c⟩ : Σ i, (fragment (ts i)).Cell)))).Nodup
  apply List.nodup_cons.mpr
  constructor
  · intro h
    obtain ⟨i, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨c, _, h⟩ := List.mem_map.mp h
    cases h
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro i _
      exact (ih i).map (fun _ _ h ↦ eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2)
    · apply (List.nodup_finRange (arity a)).imp
      intro i j hij x hx y hy hxy
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hy
      exact hij (congrArg Sigma.fst (Sum.inr.inj hxy))

/-- Every term cell appears in the parent-first traversal order. -/
theorem cellOrder_cover (t : Term arity ν) : ∀ c : t.fragment.Cell, c ∈ t.cellOrder := by
  refine PFunctor.FreeM.rec (fun _ c ↦ Fin.elim0 c) (fun a ts ih c ↦ ?_) t
  rcases c with u | ⟨i, c⟩
  · cases u
    exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
      ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨c, ih i c, rfl⟩⟩)

/-- The complete duplicate-free visit list has the compiler's finite number of cells. -/
theorem cellOrder_length (t : Term arity ν) :
    t.cellOrder.length = FinEnum.card t.fragment.Cell := by
  let e : t.fragment.Cell ≃ Fin t.cellOrder.length :=
    { toFun := fun c ↦ ⟨t.cellOrder.idxOf c,
        List.idxOf_lt_length_of_mem (t.cellOrder_cover c)⟩
      invFun := t.cellOrder.get
      left_inv := fun c ↦
        List.getElem_idxOf (List.idxOf_lt_length_of_mem (t.cellOrder_cover c))
      right_inv := fun i ↦ Fin.ext (t.cellOrder_unique.idxOf_getElem i.val i.isLt) }
  exact FiniteNet.cells_eq_of_iso (e.symm.trans t.fragment.cellEnum.equiv)

end Geb.InteractionNet.Term

end
