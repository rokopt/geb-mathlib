/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConstructorReadback
public import Geb.Prototypes.InteractionNet.GraphReadbackBoundary
public import Geb.Prototypes.InteractionNet.FiniteCells
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Whole-net read-back of a closed term graph

A term without variables has just its root boundary. After identifying that root with the
sole external port and indexing the cells, the runtime's whole-net reader agrees with the
constructor fold of the syntax. The visit list meets both completeness checks: it contains
the required number of cells and has no repetitions. No closed wire is present.

## Main statements

* {lit}`Term.fragment_indexed_readTree` — the whole indexed graph reads back its syntax tree.

## Tags

interaction net, compiler, graph, read-back, closed term, cell indexing
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Term

open scoped FinEnum

variable {α ν : Type} {arity : α → ℕ}

/-- Whole-net observation of an indexed closed fragment agrees with structural read-back. -/
theorem fragment_indexed_readTree (tag : α → Option ℕ) (t : Term arity ν)
    (e : Unit ⊕ t.fragment.Leaf ≃ Fin 1) (root : e (.inl ()) = 0) :
    FiniteNet.readTree tag
      ⟨FinEnum.card t.fragment.Cell, fun i ↦ t.fragment.label (FinEnum.equiv.symm i),
        (t.fragment.net.reboundary e).indexed⟩ = t.constructorReadback tag := by
  let n := t.fragment.net.reboundary e
  let k := FinEnum.card t.fragment.Cell
  have hb := t.fragment.net.readTree_reboundary tag e (k + 1) (.inl (.inl ()))
  change n.readTree tag (k + 1) (.inl (e (.inl ()))) =
    t.fragment.net.readTree tag (k + 1) (.inl (.inl ())) at hb
  rw [root] at hb
  have ht := t.fragment_readTree tag (k + 1) (by rw [cellOrder_length]; exact Nat.lt_succ_self k)
  have hi := n.indexedIso.readTree tag (k + 1) (.inl 0)
  change n.indexed.readTree tag (k + 1) (.inl 0) =
    (n.readTree tag (k + 1) (.inl 0)).map
      (fun r ↦ (r.1, r.2.map (FinEnum.equiv : t.fragment.Cell ≃ Fin k))) at hi
  rw [hb, ht] at hi
  have hl : n.indexed.loops = 0 := t.fragment_loops
  have hu : (t.cellOrder.map (FinEnum.equiv : t.fragment.Cell ≃ Fin k)).Nodup :=
    t.cellOrder_unique.map FinEnum.equiv.injective
  change (if n.indexed.loops ≠ 0 then none else do
    let result ← n.indexed.readTree tag (k + 1) (.inl 0)
    if result.2.length = k ∧ result.2.Nodup then some result.1 else none) = _
  rw [hl]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hi, Option.map_map, Function.comp_def]
  cases t.constructorReadback tag with
  | none => rfl
  | some r => simp [cellOrder_length, hu, k]

end Geb.InteractionNet.Term

end
