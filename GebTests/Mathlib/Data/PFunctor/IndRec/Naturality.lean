/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Naturality

/-!
# Tests for the naturality of the IR interpretation

A `delta` code over Boolean indices whose subcode depends on its
direction assignment exercises the per-summand decomposition: the
injections, the cotuple, their computation law, naturality, and
the transformation-space equivalence. Named theorems give the
`GebMeta` axiom linter declarations to inspect. The Lemma 4
naturality upgrade and its characterizing equation are exercised
at the sample code.

## Tags

inductive-recursive, interpretation, natural transformation
-/

@[expose] public section

open CategoryTheory
open IndRec IndRec.IR

/-- A sample object over the Boolean index type. -/
def sampleIObj : FreeCoprodCompDisc.{0, 0} Bool :=
  ⟨Bool, fun b ↦ b⟩

/-- The direction-dependent subcode family of `sampleNaturalityDeltaCode`. -/
def sampleDeltaSub : (PUnit → Bool) → IR.{0, 0, 0, 0} Bool Bool :=
  fun j ↦ iota Bool Bool (j PUnit.unit)

/-- A sample `delta` code whose subcode depends on the direction
assignment. -/
def sampleNaturalityDeltaCode : IR.{0, 0, 0, 0} Bool Bool :=
  delta Bool Bool PUnit sampleDeltaSub

/-- The sample delta injection evaluates a copower name to a delta
name. -/
theorem sampleDeltaInto_apply :
    (IR.deltaInto.{0, 0, 0, 0} Bool Bool PUnit sampleDeltaSub
        (fun _ ↦ true) sampleIObj).1
        ⟨⟨fun _ ↦ true, rfl⟩, ULift.up Unit.unit⟩ =
      ⟨fun _ ↦ true, ULift.up Unit.unit⟩ :=
  rfl

/-- Restricting the sample delta cotuple along the sample injection
recovers the component. -/
theorem sampleDeltaInto_desc :
    FreeCoprodCompDisc.Hom.comp Bool
        (IR.deltaInto.{0, 0, 0, 0} Bool Bool PUnit sampleDeltaSub
          (fun _ ↦ true) sampleIObj)
        (IR.deltaDesc Bool Bool PUnit sampleDeltaSub sampleIObj
          (IR.interpObj Bool Bool sampleNaturalityDeltaCode sampleIObj)
          (fun i ↦ IR.deltaInto Bool Bool PUnit sampleDeltaSub i sampleIObj)) =
      IR.deltaInto Bool Bool PUnit sampleDeltaSub (fun _ ↦ true) sampleIObj :=
  IR.deltaInto_desc Bool Bool PUnit sampleDeltaSub (fun _ ↦ true) sampleIObj
    (IR.interpObj Bool Bool sampleNaturalityDeltaCode sampleIObj)
    (fun i ↦ IR.deltaInto Bool Bool PUnit sampleDeltaSub i sampleIObj)

/-- Naturality of the sample delta injection. -/
theorem sampleDeltaInto_natural :
    FreeCoprodCompDisc.IsNatTrans Bool Bool
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{0, 0, 0} Bool ⟨PUnit, fun _ ↦ true⟩)
        (IR.interpObj Bool Bool (sampleDeltaSub (fun _ ↦ true))))
      (IR.interpObj Bool Bool sampleNaturalityDeltaCode)
      (FreeCoprodCompDisc.copowerHomMapMor
        (FreeCoprodCompDisc.lift.{0, 0, 0} Bool ⟨PUnit, fun _ ↦ true⟩)
        (IR.interpMor Bool Bool (sampleDeltaSub (fun _ ↦ true))))
      (IR.interpMor Bool Bool sampleNaturalityDeltaCode)
      (IR.deltaInto Bool Bool PUnit sampleDeltaSub (fun _ ↦ true)) :=
  IR.deltaInto_natural Bool Bool PUnit sampleDeltaSub (fun _ ↦ true)

/-- The per-summand delta decomposition round-trips the identity
transformation. -/
theorem sampleNatDeltaEquiv_roundtrip :
    (IR.natDeltaEquiv.{0, 0, 0, 0} Bool Bool PUnit sampleDeltaSub
          (IR.interpMor Bool Bool sampleNaturalityDeltaCode)).symm
        ((IR.natDeltaEquiv Bool Bool PUnit sampleDeltaSub
          (IR.interpMor Bool Bool sampleNaturalityDeltaCode))
          (FreeCoprodCompDisc.NatTrans.id
            (IR.interpObj Bool Bool sampleNaturalityDeltaCode)
            (IR.interpMor Bool Bool sampleNaturalityDeltaCode))) =
      FreeCoprodCompDisc.NatTrans.id (IR.interpObj Bool Bool sampleNaturalityDeltaCode)
        (IR.interpMor Bool Bool sampleNaturalityDeltaCode) :=
  (IR.natDeltaEquiv Bool Bool PUnit sampleDeltaSub
    (IR.interpMor Bool Bool sampleNaturalityDeltaCode)).symm_apply_apply
    (FreeCoprodCompDisc.NatTrans.id (IR.interpObj Bool Bool sampleNaturalityDeltaCode)
      (IR.interpMor Bool Bool sampleNaturalityDeltaCode))

/-- The characterizing equation of `IR.interpPrecompIso` at a concrete
`ι`-shaped code. -/
theorem sampleInterpPrecompIso_mk :
    IR.interpPrecompIso.{0, 0, 0, 0} Bool Bool
        (IR.mk Bool Bool (Sum.inl true) PEmpty.elim) =
      IR.interpPrecompIsoStep Bool Bool (Sum.inl true) PEmpty.elim
        (fun x ↦ IR.interpPrecompIso Bool Bool (PEmpty.elim x)) :=
  IR.interpPrecompIso_mk Bool Bool (Sum.inl true) PEmpty.elim

/-- Postcomposing merged-assignment values commutes with the merge at
the sample types. -/
theorem sampleArrowSumMerge_map (c : ArrowSumClassifier.{0, 0, 0} Bool Bool)
    (j : ArrowSumUnresolved c → Bool) (b : Bool) :
    Sum.map _root_.id Bool.not (arrowSumMerge c j b) =
      arrowSumMerge c (Bool.not ∘ j) b :=
  IR.arrowSumMerge_map c j Bool.not b

/-- Naturality of the Lemma 4 isomorphism family at the sample delta
code. -/
theorem samplePrecompNat :
    FreeCoprodCompDisc.IsNatTrans Bool Bool
      (IR.interpObj Bool Bool
        (IR.precomp Bool Bool PUnit (fun _ ↦ false) sampleNaturalityDeltaCode))
      (IR.precompRhsMap Bool Bool PUnit (fun _ ↦ false) sampleNaturalityDeltaCode)
      (IR.interpMor Bool Bool
        (IR.precomp Bool Bool PUnit (fun _ ↦ false) sampleNaturalityDeltaCode))
      (IR.precompRhsMapMor Bool Bool PUnit (fun _ ↦ false) sampleNaturalityDeltaCode)
      (fun k ↦ FreeCoprodCompDisc.Iso.hom Bool
        (IR.interpPrecompIso Bool Bool sampleNaturalityDeltaCode PUnit
          (fun _ ↦ false) k)) :=
  IR.interpPrecompIso_natural Bool Bool sampleNaturalityDeltaCode PUnit (fun _ ↦ false)
