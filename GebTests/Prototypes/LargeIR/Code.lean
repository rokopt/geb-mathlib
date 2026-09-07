/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.LargeIR.Basic
public import Geb.Prototypes.LargeIR.Code -- shake: keep

/-!
# Tests for the transcription read back as a large inductive-recursive code

Exercises `Geb.Prototypes.LargeIR.Code` on the functor `A ↦ A true × A false`
and the object `Fin 3 → Bool` of `GebTests.Prototypes.LargeIR.Basic`: the
code's interpretation at the family of the input computes to the expected
index type and decodings, and the isomorphism with the transcription's output
presheaf sends the comparison map's element to the `δ` assignment `id` and the
element over `not` to the `δ` assignment `not`, each with the expected decoded
fibre.

## Tags

prototype, inductive-recursive, code, walking arrow, reduction test
-/

@[expose] public section

open CategoryTheory PresheafIRUniv IndRec GebProto.LargeIR

namespace LargeIRTest

/-! ## The code's interpretation computes -/

-- The index type of the interpretation: a `σ` index in `Unit`, a `δ`
-- assignment `Bool → Bool`, and the `ι` point.
example : (IR.interpObj Type Type (code piBool) (famOfPsh (ofSlice p3))).1 =
    (Σ _ : Unit, Σ _ : Bool → Bool, ULift Unit) :=
  rfl

-- The decoding at the assignment `not`: the fibre of the functor applied to
-- the family `p3` pulled back along `not`.
example : (IR.interpObj Type Type (code piBool) (famOfPsh (ofSlice p3))).2 ⟨(), not, ⟨()⟩⟩ =
    fibreValue piBool () ((famOfPsh (ofSlice p3)).2 ∘ not) :=
  rfl

-- The family of the input: `Bool`, decoding `u` to the fibre of `p3` over `u`.
example : (famOfPsh (ofSlice p3)).1 = Bool := rfl
example : (famOfPsh (ofSlice p3)).2 true = { i : Fin 3 // p3 i = true } := rfl

/-! ## The isomorphism with the transcription's output presheaf -/

/-- The comparison map's element, read through the isomorphism as an element
of the code's interpretation. -/
def sampleDecoded :
    (pshOfFam (IR.interpObj Type Type (code piBool) (famOfPsh (ofSlice p3)))).obj ⟨1⟩ :=
  (arrowPshCodeEquiv piBool (ofSlice p3)).total ⟨sample, rfl⟩

-- Its index is the `δ` assignment `id`.
example : sampleDecoded.1 = ⟨(), id, ⟨()⟩⟩ := rfl

-- Its decoded fibre sends the direction `true` to `0` and `false` to `1`.
example : (sampleDecoded.2.2 true).1 = (0 : Fin 3) := rfl
example : (sampleDecoded.2.2 false).1 = (1 : Fin 3) := rfl

/-- The element over `not`, read through the isomorphism. -/
def sampleNotDecoded :
    (pshOfFam (IR.interpObj Type Type (code piBool) (famOfPsh (ofSlice p3)))).obj ⟨1⟩ :=
  (arrowPshCodeEquiv piBool (ofSlice p3)).total ⟨sampleNot, rfl⟩

-- Its index is the `δ` assignment `not`: the base map of the transcription's
-- value is the `δ` rule's assignment `g : A → U`.
example : sampleNotDecoded.1 = ⟨(), not, ⟨()⟩⟩ := rfl

-- Its decoded fibre sends the direction `true` to `1`, an element over
-- `not true = false`.
example : (sampleNotDecoded.2.2 true).1 = (1 : Fin 3) := rfl

-- The isomorphism commutes with the restriction: the level-`0` image of the
-- element over `not` is its index.
example : (arrowPshCodeEquiv piBool (ofSlice p3)).base
    (((arrowPsh piBool).objPresheaf (ofSlice p3)).map waHom.op ⟨sampleNot, rfl⟩) =
      ⟨(), not, ⟨()⟩⟩ :=
  ((arrowPshCodeEquiv piBool (ofSlice p3)).map_total ⟨sampleNot, rfl⟩).symm

end LargeIRTest
