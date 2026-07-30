/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tests for the choice-free product encoding of `Fin`

A sample pairing through `finProdFinEquivC` computes to its expected
index and round-trips back to the pair.

## Tags

fin, equiv, product
-/

@[expose] public section

/-- A sample pairing through the product encoding. -/
def sampleProdEncode : Fin (3 * 4) := finProdFinEquivC ((2 : Fin 3), (1 : Fin 4))

/-- The sample pairing is the index `9`. -/
theorem sampleProdEncode_eq : sampleProdEncode = (9 : Fin (3 * 4)) := rfl

/-- The product encoding round-trips at the sample pair. -/
theorem sampleProdEncode_roundtrip :
    finProdFinEquivC.symm sampleProdEncode = ((2 : Fin 3), (1 : Fin 4)) := rfl
