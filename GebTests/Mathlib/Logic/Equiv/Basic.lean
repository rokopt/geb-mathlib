/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Logic.Equiv.Basic

/-!
# Tests for eliminators for sections of sigma-type projections

A round-trip test exercises `sigmaCongrRight'` on a sample dependent
pair.

## Tags

sigma, equiv
-/

@[expose] public section

/-- `sigmaCongrRight'` round-trips a sample dependent pair. -/
theorem sampleSigmaCongrRight'_roundtrip :
    (sigmaCongrRight' (fun _ : Bool ↦ Equiv.refl Nat)).symm
      (sigmaCongrRight' (fun _ : Bool ↦ Equiv.refl Nat) ⟨true, 3⟩) =
      ⟨true, 3⟩ :=
  rfl
