/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Fin.Basic

/-!
# Tests for choice-free division, remainder and pairing on `Fin`

A sample pairing at `Fin (3 * 4)` computes to its expected index, its
quotient and remainder recover the pairing's two components, and the
three operations round-trip at that index.

## Tags

fin, division, remainder, pairing
-/

@[expose] public section

/-- A sample pairing: quotient `2`, remainder `1`, at `3 * 4`. -/
def samplePairC : Fin (3 * 4) := Fin.pairC (2 : Fin 3) (1 : Fin 4)

/-- The sample pairing is the index `9`. -/
theorem samplePairC_eq : samplePairC = (9 : Fin (3 * 4)) := rfl

/-- The sample pairing's quotient is its first component. -/
theorem samplePairC_divNatC : Fin.divNatC samplePairC = 2 := rfl

/-- The sample pairing's remainder is its second component. -/
theorem samplePairC_modNatC : Fin.modNatC samplePairC = 1 := rfl

/-- The three operations round-trip at the sample index. -/
theorem samplePairC_roundtrip :
    Fin.pairC (Fin.divNatC samplePairC) (Fin.modNatC samplePairC) =
      samplePairC := rfl
