/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Vector.NodupEquivFin

/-!
# Tests for the injective-vector inversion

A sample injective vector round-trips through `invOfInjective`.

## Tags

vector, injective, equiv
-/

@[expose] public section

/-- A sample injective vector. -/
def sampleInj : Vector (Fin 5) 3 :=
  Vector.ofFnC (fun i ↦ ⟨i.1 + 1, by omega⟩)

/-- It is injective on indices. -/
theorem sampleInj_injective : Function.Injective sampleInj.get := by
  intro a b hab
  simp only [sampleInj, Vector.get_ofFnC] at hab
  have : a.1 + 1 = b.1 + 1 := congrArg Fin.val hab
  exact Fin.ext (by omega)

/-- The inversion round-trips a sample index. -/
theorem sampleInj_roundtrip (i : Fin 3) :
    (Vector.invOfInjective sampleInj sampleInj_injective).symm
      (Vector.invOfInjective sampleInj sampleInj_injective i) = i :=
  (Vector.invOfInjective sampleInj sampleInj_injective).left_inv i

/-- The inversion carries the sample vector's entries. -/
theorem sampleInj_value (i : Fin 3) :
    ((Vector.invOfInjective sampleInj sampleInj_injective i) : Fin 5)
      = sampleInj.get i := rfl

/-- The inverse carries a sample member back to its concrete index. -/
theorem sampleInj_value_symm :
    (Vector.invOfInjective sampleInj sampleInj_injective).symm
      (⟨sampleInj.get 1, List.mem_of_getElem rfl⟩ :
        {j : Fin 5 // j ∈ sampleInj.toList}) = 1 := rfl
