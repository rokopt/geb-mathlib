/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Functor

/-!
# Tests for the functoriality of the IR interpretation

The characterizing equations of `IR.interpMor` are exercised at
concrete codes over the unit index types; the functor laws
(preservation of identity and composition) are exercised at a
sample object and endomorphism, with the identity law also
exercised at a `delta` code. Named theorems give the `GebMeta`
axiom linter declarations to inspect.

## Tags

inductive-recursive, interpretation, functor
-/

@[expose] public section

open CategoryTheory
open IndRec IndRec.IR

/-- The characterizing equation of `interpMor` at a concrete `iota`
code. -/
theorem sampleInterpMor_iota :
    IR.interpMor.{0, 0, 0, 0} PUnit PUnit (iota PUnit PUnit PUnit.unit) =
      IR.interpMorIota.{0, 0, 0, 0} PUnit PUnit PUnit.unit :=
  IR.interpMor_iota PUnit PUnit PUnit.unit

/-- The characterizing equation of `interpMor` at a concrete `sigma`
code. -/
theorem sampleInterpMor_sigma :
    IR.interpMor.{0, 0, 0, 0} PUnit PUnit
        (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit)) =
      IR.interpMorSigma PUnit PUnit Bool
        (fun _ ↦ IR.interpObj PUnit PUnit (iota PUnit PUnit PUnit.unit))
        (fun _ ↦ IR.interpMor PUnit PUnit (iota PUnit PUnit PUnit.unit)) :=
  IR.interpMor_sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit)

/-- The characterizing equation of `interpMor` at a concrete `delta`
code. -/
theorem sampleInterpMor_delta :
    IR.interpMor.{0, 0, 0, 0} PUnit PUnit
        (delta PUnit PUnit PUnit (fun _ ↦ iota PUnit PUnit PUnit.unit)) =
      IR.interpMorDelta PUnit PUnit PUnit
        (fun _ ↦ IR.interpObj PUnit PUnit (iota PUnit PUnit PUnit.unit))
        (fun _ ↦ IR.interpMor PUnit PUnit (iota PUnit PUnit PUnit.unit)) :=
  IR.interpMor_delta PUnit PUnit PUnit (fun _ ↦ iota PUnit PUnit PUnit.unit)

/-- A sample object of the completion over the unit type. -/
def sampleObj : FreeCoprodCompDisc.{0, 0} PUnit :=
  ⟨Bool, fun _ ↦ PUnit.unit⟩

/-- Preservation of identity at a concrete `sigma` code and the
sample object. -/
theorem sampleInterpMor_id :
    IR.interpMor.{0, 0, 0, 0} PUnit PUnit
        (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
        sampleObj sampleObj
        (FreeCoprodCompDisc.Hom.id PUnit sampleObj) =
      FreeCoprodCompDisc.Hom.id PUnit
        (IR.interpObj PUnit PUnit
          (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
          sampleObj) :=
  IR.interpMor_id PUnit PUnit
    (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
    sampleObj

/-- A sample endomorphism of `sampleObj`. -/
def sampleObjHom : FreeCoprodCompDisc.Hom PUnit sampleObj sampleObj :=
  ⟨_root_.id, rfl⟩

/-- Preservation of composition at a concrete `sigma` code and the
sample endomorphism. -/
theorem sampleInterpMor_comp :
    IR.interpMor.{0, 0, 0, 0} PUnit PUnit
        (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
        sampleObj sampleObj
        (FreeCoprodCompDisc.Hom.comp PUnit sampleObjHom sampleObjHom) =
      FreeCoprodCompDisc.Hom.comp PUnit
        (IR.interpMor PUnit PUnit
          (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
          sampleObj sampleObj sampleObjHom)
        (IR.interpMor PUnit PUnit
          (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
          sampleObj sampleObj sampleObjHom) :=
  IR.interpMor_comp PUnit PUnit
    (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
    sampleObj sampleObj sampleObj sampleObjHom sampleObjHom

/-- Preservation of identity at a concrete `delta` code and the
sample object. -/
theorem sampleInterpMor_id_delta :
    IR.interpMor.{0, 0, 0, 0} PUnit PUnit
        (delta PUnit PUnit PUnit (fun _ ↦ iota PUnit PUnit PUnit.unit))
        sampleObj sampleObj
        (FreeCoprodCompDisc.Hom.id PUnit sampleObj) =
      FreeCoprodCompDisc.Hom.id PUnit
        (IR.interpObj PUnit PUnit
          (delta PUnit PUnit PUnit (fun _ ↦ iota PUnit PUnit PUnit.unit))
          sampleObj) :=
  IR.interpMor_id PUnit PUnit
    (delta PUnit PUnit PUnit (fun _ ↦ iota PUnit PUnit PUnit.unit))
    sampleObj
