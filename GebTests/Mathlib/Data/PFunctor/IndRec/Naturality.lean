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
at the sample code. The ∅-evaluation and `InnerHom` fiber
equivalences are exercised at `ι`-codes. The plus-lift bridge
morphisms and transformations are exercised at the sample object
and code. Theorem 3 is exercised at concrete morphisms: a
component application, a `delta` morphism action with a
propositionally nontrivial commutation proof (observing the
`FreeCoprodCompDisc.homOfEq` transport in `IR.interpMorDelta`),
and the round-trip laws at `ι`-, `σ`-, and `δ`-domain morphisms.

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

/-- The ∅-evaluation equivalence evaluates the identity transformation
to the identity on the singleton name type. -/
theorem sampleNatIotaEquiv_apply :
    ((IR.natIotaEquiv.{0, 0, 0, 0} Bool Bool true (iota Bool Bool true))
        (FreeCoprodCompDisc.NatTrans.id
          (IR.interpObj Bool Bool (iota Bool Bool true))
          (IR.interpMor Bool Bool (iota Bool Bool true)))).1
        (ULift.up Unit.unit) =
      ULift.up Unit.unit :=
  rfl

/-- The `InnerHom` fiber equivalence sends the reflexivity witness to
the singleton name. -/
theorem sampleInnerHomEquiv_apply :
    ((IR.innerHomEquiv.{0, 0, 0, 0} Bool Bool true (iota Bool Bool true))
        (ULift.up (PLift.up rfl))).1 =
      ULift.up Unit.unit :=
  rfl

/-- The forward bridge followed by the backward bridge is the identity
at the sample object. -/
theorem samplePlusLiftBridge_hom_invHom :
    FreeCoprodCompDisc.Hom.comp Bool
        (IR.plusLiftBridgeHom Bool PUnit (fun _ ↦ false) sampleIObj)
        (IR.plusLiftBridgeInvHom Bool PUnit (fun _ ↦ false) sampleIObj) =
      FreeCoprodCompDisc.Hom.id Bool
        (FreeCoprodCompDisc.plus Bool
          (FreeCoprodCompDisc.lift.{0, 0, 0} Bool ⟨PUnit, fun _ ↦ false⟩)
          sampleIObj) :=
  IR.plusLiftBridge_hom_invHom Bool PUnit (fun _ ↦ false) sampleIObj

/-- The two bridge transformations are inverse at the sample delta
code. -/
theorem samplePlusLiftBridgeNat_isInverse :
    FreeCoprodCompDisc.NatTrans.IsInverse
        (IR.plusLiftBridgeNat Bool Bool PUnit (fun _ ↦ false) sampleNaturalityDeltaCode)
        (IR.plusLiftBridgeNatInv Bool Bool PUnit (fun _ ↦ false)
          sampleNaturalityDeltaCode) :=
  IR.plusLiftBridgeNat_isInverse Bool Bool PUnit (fun _ ↦ false)
    sampleNaturalityDeltaCode

/-- A sample code morphism between `ι`-codes: the reflexivity
witness. -/
def sampleIotaHom :
    IR.Hom.{0, 0, 0, 0} Bool Bool (iota Bool Bool true)
      (iota Bool Bool true) :=
  ULift.up (PLift.up rfl)

/-- The interpretation of `sampleIotaHom` as a natural transformation:
its component at the sample object is the identity on the singleton
name type. -/
theorem sampleInterpHom_component :
    ((IR.interpHom.{0, 0, 0, 0} Bool Bool (iota Bool Bool true)
          (iota Bool Bool true) sampleIotaHom).1 sampleIObj).1
        (ULift.up Unit.unit) =
      ULift.up Unit.unit :=
  rfl

/-- A domain object with constant decoding. -/
def sampleActX : FreeCoprodCompDisc.{0, 0} Bool :=
  ⟨Bool, fun _ ↦ true⟩

/-- A codomain object whose decoding agrees with the constant one only
propositionally. -/
def sampleActY : FreeCoprodCompDisc.{0, 0} Bool :=
  ⟨Bool, fun b ↦ b || true⟩

/-- A morphism whose commutation proof is propositionally nontrivial:
the identity index function, with decodings equal by `Bool.or_true`
rather than by reflexivity. -/
def sampleActHom : FreeCoprodCompDisc.Hom Bool sampleActX sampleActY :=
  ⟨fun b ↦ b, funext (fun b ↦ Bool.or_true b)⟩

/-- The morphism action of the interpretation at `sampleNaturalityDeltaCode` and
`sampleActHom`: the `homOfEq` transport in `IR.interpMorDelta` is taken
along the propositionally nontrivial commutation proof, and the image
name is observable. -/
theorem sampleInterpMorDelta_action :
    (IR.interpMor.{0, 0, 0, 0} Bool Bool sampleNaturalityDeltaCode sampleActX
          sampleActY sampleActHom).1
        ⟨fun _ ↦ false, ULift.up Unit.unit⟩ =
      ⟨fun _ ↦ false, ULift.up Unit.unit⟩ :=
  congrFun
    (congrArg Subtype.val
      (congrFun (congrFun (congrFun
        (IR.interpMor_delta Bool Bool PUnit sampleDeltaSub) sampleActX)
        sampleActY) sampleActHom))
    ⟨fun _ ↦ false, ULift.up Unit.unit⟩

/-- The decoding of the image agrees with the decoding of the argument:
the interpretation's morphism action commutes with the decodings. -/
theorem sampleInterpMorDelta_action_decode :
    (IR.interpObj Bool Bool sampleNaturalityDeltaCode sampleActY).2
        ((IR.interpMor.{0, 0, 0, 0} Bool Bool sampleNaturalityDeltaCode sampleActX
              sampleActY sampleActHom).1
          ⟨fun _ ↦ false, ULift.up Unit.unit⟩) =
      true :=
  congrFun
    (IR.interpMor Bool Bool sampleNaturalityDeltaCode sampleActX sampleActY
        sampleActHom).2
    ⟨fun _ ↦ false, ULift.up Unit.unit⟩

/-- A sample code morphism out of a `σ`-code: componentwise reflexivity
witnesses. -/
def sampleSigmaToIotaHom :
    IR.Hom.{0, 0, 0, 0} Bool Bool
      (sigma Bool Bool Bool (fun _ ↦ iota Bool Bool true))
      (iota Bool Bool true) :=
  fun _ ↦ ULift.up (PLift.up rfl)

/-- `IR.natToHom` inverts `IR.interpHom` at the sample `ι`-morphism. -/
theorem sampleNatToHom_interpHom :
    IR.natToHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
        (IR.interpHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
          sampleIotaHom) =
      sampleIotaHom :=
  IR.natToHom_interpHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
    sampleIotaHom

/-- `IR.natToHom` inverts `IR.interpHom` at the sample `σ`-morphism. -/
theorem sampleSigmaNatToHom_interpHom :
    IR.natToHom Bool Bool (sigma Bool Bool Bool (fun _ ↦ iota Bool Bool true))
        (iota Bool Bool true)
        (IR.interpHom Bool Bool
          (sigma Bool Bool Bool (fun _ ↦ iota Bool Bool true))
          (iota Bool Bool true) sampleSigmaToIotaHom) =
      sampleSigmaToIotaHom :=
  IR.natToHom_interpHom Bool Bool
    (sigma Bool Bool Bool (fun _ ↦ iota Bool Bool true))
    (iota Bool Bool true) sampleSigmaToIotaHom

/-- `IR.interpHom` inverts `IR.natToHom` at the interpretation of the
sample `ι`-morphism. -/
theorem sampleInterpHom_natToHom :
    IR.interpHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
        (IR.natToHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
          (IR.interpHom Bool Bool (iota Bool Bool true)
            (iota Bool Bool true) sampleIotaHom)) =
      IR.interpHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
        sampleIotaHom :=
  IR.interpHom_natToHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
    (IR.interpHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
      sampleIotaHom)

/-- The identity morphism of the sample `δ`-code (`IR.id`), the
domain for the `δ`-branch exercise of Theorem 3. -/
def sampleDeltaId :
    IR.Hom.{0, 0, 0, 0} Bool Bool sampleNaturalityDeltaCode sampleNaturalityDeltaCode :=
  IR.id Bool Bool sampleNaturalityDeltaCode

/-- Theorem 3's forward map specialized at a `δ`-domain morphism:
the identity of the sample `δ`-code as a natural transformation
(`IR.interpHomEquiv` computes only propositionally through
`IR.rec`, so the specialization is type-level). -/
def sampleDeltaIdNat :
    FreeCoprodCompDisc.NatTrans Bool Bool
      (IR.interpObj Bool Bool sampleNaturalityDeltaCode)
      (IR.interpObj Bool Bool sampleNaturalityDeltaCode)
      (IR.interpMor Bool Bool sampleNaturalityDeltaCode)
      (IR.interpMor Bool Bool sampleNaturalityDeltaCode) :=
  IR.interpHom Bool Bool sampleNaturalityDeltaCode sampleNaturalityDeltaCode sampleDeltaId

/-- The `δ`-domain round trip: `IR.natToHom` recovers the identity
morphism from its interpretation. -/
theorem sampleDeltaId_roundTrip :
    IR.natToHom Bool Bool sampleNaturalityDeltaCode sampleNaturalityDeltaCode
        sampleDeltaIdNat =
      sampleDeltaId :=
  IR.natToHom_interpHom Bool Bool sampleNaturalityDeltaCode sampleNaturalityDeltaCode
    sampleDeltaId
