/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Vector.OfFn

/-!
# Tests for the choice-free `ofFn`

`ofFnC` computes a sample vector's entries, a sample index function
round-trips through `ofFnC` in both directions, and the
`get`/`getElem` bridge holds at a sample index.

## Tags

vector, ofFn
-/

@[expose] public section

/-- A sample index function. -/
def sampleIdx : Fin 3 → Nat := fun i ↦ 2 * i.1

/-- The sample vector built from it. -/
def sampleVec : Vector Nat 3 := Vector.ofFnC sampleIdx

/-- `ofFnC` computes the sample vector's entries. -/
theorem sampleVec_value : sampleVec.get ⟨1, by omega⟩ = 2 := rfl

/-- `ofFnC` recovers the sample function pointwise. -/
theorem sampleVec_get (i : Fin 3) : sampleVec.get i = sampleIdx i :=
  Vector.get_ofFnC sampleIdx i

/-- `ofFnC` inverts indexing on the sample vector. -/
theorem sampleVec_roundtrip : Vector.ofFnC sampleVec.get = sampleVec :=
  Vector.ofFnC_get sampleVec

/-- The bridge holds at a sample index. -/
theorem sampleVec_bridge : sampleVec.get ⟨1, by omega⟩ = sampleVec[1] :=
  Vector.get_eq_getElem sampleVec ⟨1, by omega⟩
