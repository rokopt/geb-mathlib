/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.List.NodupEquivFin

/-!
# Tests for the choice-free list inversion

A sample duplicate-free list round-trips through `getEquivC`, and
`compressEquiv` renumbers a sample predicate's indices.

## Tags

list, nodup, equiv
-/

@[expose] public section

/-- A sample duplicate-free list. -/
def sampleList : List Nat := [7, 3, 5]

/-- It is duplicate-free. -/
theorem sampleList_nodup : sampleList.Nodup := by decide

/-- `getEquivC` round-trips a sample index. -/
theorem sampleList_roundtrip :
    (List.Nodup.getEquivC sampleList sampleList_nodup).symm
      (List.Nodup.getEquivC sampleList sampleList_nodup ⟨1, by decide⟩) =
      ⟨1, by decide⟩ :=
  (List.Nodup.getEquivC sampleList sampleList_nodup).left_inv _

/-- `getEquivC` carries index `1` to the sample list's second entry. -/
theorem sampleList_getEquivC_forward :
    (List.Nodup.getEquivC sampleList sampleList_nodup ⟨1, by decide⟩ : {x // x ∈ sampleList}).1
      = 3 := rfl

/-- `getEquivC` carries the sample list's second entry back to index `1`. -/
theorem sampleList_getEquivC_backward :
    (List.Nodup.getEquivC sampleList sampleList_nodup).symm ⟨3, by decide⟩ = ⟨1, by decide⟩ := rfl

/-- A sample decidable predicate on `Fin 4`. -/
def samplePred : Fin 4 → Bool := fun i ↦ decide (i.1 % 2 = 0)

/-- `compressEquiv` round-trips a sample compressed index. -/
theorem sampleCompress_roundtrip
    (i : Fin ((List.finRange 4).filter samplePred).length) :
    (Fin.compressEquiv samplePred).symm (Fin.compressEquiv samplePred i) = i :=
  (Fin.compressEquiv samplePred).left_inv i

/-- `compressEquiv` carries the second compressed index to the sample
predicate's second even residue. -/
theorem sampleCompress_value :
    (Fin.compressEquiv samplePred ⟨1, by decide⟩ : {i : Fin 4 // samplePred i}).1 = 2 := rfl
