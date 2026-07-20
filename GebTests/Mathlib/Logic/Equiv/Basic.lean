/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Logic.Equiv.Basic

/-!
# Tests for sigma-type congruence and classification

Round-trip tests exercise `sigmaCongrRight'`,
`arrowSumEquivSigma`, and `sigmaCompEquivSigmaFiber` on sample
inputs. The sigma–subtype commutation and the empty-valued
function-type equivalence round-trip at sample instances.

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

/-- A sample function into a sum, hitting both components. -/
def sampleArrow : Bool → Nat ⊕ Bool :=
  fun b ↦ if b then Sum.inl 0 else Sum.inr true

/-- The classification equivalence round-trips the sample
function pointwise. -/
theorem sampleArrow_roundtrip (b : Bool) :
    (arrowSumEquivSigma Bool Nat Bool).symm
      (arrowSumEquivSigma Bool Nat Bool sampleArrow) b =
      sampleArrow b :=
  Bool.casesOn b rfl rfl

/-- The fiber-grouping equivalence round-trips a sample pair. -/
theorem sampleSigmaFiber_roundtrip :
    (sigmaCompEquivSigmaFiber Bool.not (fun _ ↦ Nat)).symm
      (sigmaCompEquivSigmaFiber Bool.not (fun _ ↦ Nat) ⟨true, 3⟩) =
      ⟨true, 3⟩ :=
  rfl

/-- Commuting a sigma with a fiberwise subtype round-trips. -/
theorem sampleSigmaSubtypeEquiv_roundtrip :
    (sigmaSubtypeEquiv (fun _ : Bool ↦ Bool) (fun a n ↦ a = n)).symm
        ((sigmaSubtypeEquiv (fun _ : Bool ↦ Bool) (fun a n ↦ a = n))
          ⟨true, ⟨true, rfl⟩⟩) =
      ⟨true, ⟨true, rfl⟩⟩ :=
  rfl

/-- The empty-valued function types across universes are equivalent:
the round trip is the identity. -/
theorem sampleArrowPEmptyEquiv_roundtrip (e : Bool → PEmpty.{1}) :
    (arrowPEmptyEquiv.{0, 1, 0} Bool).symm
        (arrowPEmptyEquiv.{0, 1, 0} Bool e) = e :=
  (arrowPEmptyEquiv.{0, 1, 0} Bool).symm_apply_apply e
