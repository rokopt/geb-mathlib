/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.LargeIR.Code
public import Geb.Prototypes.LargeIR.Morphism -- shake: keep

/-!
# Tests for the agreement of the transcription and the code on morphisms

Exercises `Geb.Prototypes.LargeIR.Morphism` on a morphism of walking-arrow
presheaves over a base change: the square with base map `not` from the
object `Fin 3 → Bool` of `GebTests.Prototypes.LargeIR.Basic` to its
composite with `not`. Its morphism of families has base `not`, the code's
action sends the `δ` assignment `id` to `not`, and the naturality of the
isomorphism carries the comparison map's element, read through the
isomorphism, to the element with that assignment.

## Tags

prototype, inductive-recursive, code, walking arrow, naturality, reduction
test
-/

@[expose] public section

open CategoryTheory PresheafIRUniv IndRec GebProto.LargeIR

namespace LargeIRTest

/-! ## A morphism over a base change -/

/-- The square with base map `not` and total map the identity, from `p3` to
`not ∘ p3`, as a morphism of walking-arrow presheaves. -/
def flipHom : NatTrans (ofSlice p3) (ofSlice (not ∘ p3)) :=
  arrowHom not id rfl

-- Its morphism of families has base `not`.
example : (famHomOfNatTrans flipHom).1 = not := rfl

-- The code's action sends the `δ` assignment `id` to `not`.
example : (codeMap piBool (famHomOfNatTrans flipHom)).1 ⟨(), id, ⟨()⟩⟩ = ⟨(), not, ⟨()⟩⟩ :=
  rfl

-- The action is functorial.
example : codeMap piBool (FamHom.id (famOfPsh (ofSlice p3))) = FamHom.id _ :=
  codeMap_id piBool _

/-! ## Naturality at the comparison map's element -/

/-- The comparison map's element, read through the isomorphism, carried along
the code's action of the square. -/
def sampleFlipped :
    (pshOfFam (IR.interpObj Type Type (code piBool) (famOfPsh (ofSlice (not ∘ p3))))).obj ⟨1⟩ :=
  (natTransOfFamHom (codeMap piBool (famHomOfNatTrans flipHom))).app ⟨1⟩ sampleDecoded

-- The transcription's action on the element, read through the isomorphism,
-- is the code's action on the element read through the isomorphism.
example : (arrowPshCodeEquiv piBool (ofSlice (not ∘ p3))).total
    (((arrowPsh piBool).mapPresheaf flipHom).app ⟨1⟩ ⟨sample, rfl⟩) = sampleFlipped :=
  total_map piBool flipHom ⟨sample, rfl⟩

-- Its index is the `δ` assignment `not`.
example : sampleFlipped.1 = ⟨(), not, ⟨()⟩⟩ := rfl

-- Its decoded fibre is the original one, the total map being the identity.
example : (sampleFlipped.2.2 true).1 = (0 : Fin 3) := rfl

end LargeIRTest
