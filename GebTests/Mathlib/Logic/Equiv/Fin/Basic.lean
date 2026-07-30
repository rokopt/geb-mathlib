/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Logic.Equiv.Fin.Basic
-- `Mathlib.Tactic.Attr.Core` tags `id` with `mfld_simps`; `lake shake` treats
-- any reference to `id` as depending on the tagging module.
import Mathlib.Tactic.Attr.Core

/-!
# Tests for the choice-free product and exponential encodings of `Fin`

A sample pairing through `finProdFinEquivC` computes to its expected
index and round-trips back to the pair. A sample function encoded
through `Fin.funEncodeC` computes to its expected index and
round-trips back to the function.

## Tags

fin, equiv, product, exponential
-/

@[expose] public section

/-- A sample pairing through the product encoding. -/
def sampleProdEncode : Fin (3 * 4) := finProdFinEquivC ((2 : Fin 3), (1 : Fin 4))

/-- The sample pairing is the index `9`. -/
theorem sampleProdEncode_eq : sampleProdEncode = (9 : Fin (3 * 4)) := rfl

/-- The product encoding round-trips at the sample pair. -/
theorem sampleProdEncode_roundtrip :
    finProdFinEquivC.symm sampleProdEncode = ((2 : Fin 3), (1 : Fin 4)) := rfl

/-- A sample function encoded through the exponential encoding. -/
def sampleFunEncode : Fin (3 ^ 2) :=
  Fin.funEncodeC (fun i : Fin 2 ↦ (⟨i.val, by omega⟩ : Fin 3))

/-- The sample encoding is the index `1`: the pairing puts the head
digit high, so the function sending `0` to `0` and `1` to `1`
encodes as `0 * 3 + 1`. -/
theorem sampleFunEncode_eq : sampleFunEncode = (1 : Fin (3 ^ 2)) := by decide

/-- The exponential encoding round-trips at the sample function. -/
theorem sampleFunEncode_roundtrip (i : Fin 2) :
    Fin.funDecodeC sampleFunEncode i = (⟨i.val, by omega⟩ : Fin 3) := by
  simp only [sampleFunEncode, Fin.funDecodeC_funEncodeC]

/-- The decode direction computes at the encoded literal. -/
theorem sampleFunDecode_eq (i : Fin 2) :
    Fin.funDecodeC (1 : Fin (3 ^ 2)) i = (⟨i.val, by omega⟩ : Fin 3) := by
  revert i; decide
