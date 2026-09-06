/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LargeIR -- shake: keep

/-!
# Tests for the walking-arrow transcription of a slice polynomial functor

Exercises `Geb.Prototypes.LargeIR` on the slice polynomial functor
`Type/Bool → Type/Unit` with one shape and the two directions `Bool`, the
direction-input map the identity, whose value at a family is the product of
the family's two fibres. The tests compute the transcription's shapes and
restrictions, and its value at the walking-arrow presheaf of an object
`Fin 3 → Bool` of `Type/Bool`: the comparison map lands at level `1` over the
identity base map and restricts to the level-`0` element `((), id)`, and a
level-`1` element over the base map `not` — the pullback of the object along
`not`, which the slice functor alone cannot express — restricts to
`((), not)`.

## Tags

prototype, presheaf, walking arrow, slice polynomial functor, reduction test
-/

@[expose] public section

open CategoryTheory PresheafIRUniv GebProto.LargeIR

namespace LargeIRTest

/-! ## The slice polynomial functor -/

/-- The slice polynomial functor `Type/Bool → Type/Unit` with one shape and the
two directions `Bool`, the direction-input map the identity: its value at a
family over `Bool` is the product of the family's two fibres. -/
def piBool : SlicePFunctor.{0, 0, 0, 0} Bool Unit where
  toSliceDomPFunctor := SliceDomPFunctor.representable Bool id
  q := fun _ ↦ ()

/-! ## Shapes, directions, and their restrictions -/

-- The level-`0` shape lies over `0` and the level-`1` shape over `1`.
example : (arrowPsh piBool).q (.inl ()) = 0 := rfl
example : (arrowPsh piBool).q (.inr PUnit.unit) = 1 := rfl

-- The level-`1` shape restricts to the level-`0` shape at its output index.
example : restrShape piBool 0 (.inr PUnit.unit) = .inl () := rfl

-- A level-`1` direction restricts to the level-`0` direction at its input
-- index.
example : restrDir piBool (.inr PUnit.unit) 0 (.inr true) = .inl true := rfl

-- Every shape has the level-`0` directions `Bool`.
example : (arrowPsh piBool).B (.inl ()) = (Bool ⊕ PEmpty) := rfl
example : (arrowPsh piBool).B (.inr PUnit.unit) = (Bool ⊕ Bool) := rfl

/-! ## The value at an object of `Type/Bool` -/

/-- An object of `Type/Bool`: `Fin 3` over `Bool`, `0` over `true` and the
rest over `false`. -/
def p3 : Fin 3 → Bool := fun i ↦ decide (i = 0)

/-- An element of the slice functor's value at `p3`: `true ↦ 0`, `false ↦ 1`. -/
def elt : piBool.toSliceDomPFunctor.Obj p3 :=
  ⟨⟨PUnit.unit, fun b ↦ cond b (0 : Fin 3) 1⟩, funext fun b ↦ by cases b <;> rfl⟩

/-- The comparison map at `elt`. -/
def sample : (arrowPsh piBool).obj (ofSlice p3) := cmp piBool p3 elt

-- The comparison map lands at level `1` over the identity base map.
example : objEquiv piBool (ofSlice p3) sample = .inr ⟨id, (pullbackIdEquiv piBool p3).symm elt⟩ :=
  objEquiv_cmp piBool p3 elt

-- Its restriction along `0 ⟶ 1` is the level-`0` element `((), id)`.
example : toLevels piBool (ofSlice p3) ((arrowPsh piBool).objRestr waHom sample rfl) =
    .inl ((), id) :=
  toLevels_objRestr_cmp piBool p3 elt

-- The level-`0` part of the value reads back the base map.
example : toLevels piBool (ofSlice p3) (ofLevels piBool (ofSlice p3) (.inl ((), not))) =
    .inl ((), not) :=
  rfl

/-! ## A level-`1` element over a non-identity base map -/

/-- An element of the slice functor's value at the pullback of `p3` along
`not`: over `true` an element of `Fin 3` lying over `false`, over `false` one
lying over `true`. -/
def eltNot : piBool.toSliceDomPFunctor.Obj (pullbackProj (ofSlice p3) not) :=
  ⟨⟨PUnit.unit, fun b ↦ ⟨b, (cond b 1 0 : Fin 3), by cases b <;> rfl⟩⟩,
    funext fun _ ↦ rfl⟩

/-- The level-`1` element over `not`. -/
def sampleNot : (arrowPsh piBool).obj (ofSlice p3) :=
  ofLevels piBool (ofSlice p3) (.inr ⟨not, eltNot⟩)

-- It restricts along `0 ⟶ 1` to the level-`0` element `((), not)`: the base
-- map is data of the transcription's value, not fixed by the input.
example : toLevels piBool (ofSlice p3) ((arrowPsh piBool).objRestr waHom sampleNot rfl) =
    .inl ((), not) :=
  rfl

-- The two elements' level-`1` assignments differ: `sample` sends the direction
-- `true` to `0`, `sampleNot` to `1`.
example : sample.1.1.2 (.inr true) = ⟨1, (0 : Fin 3)⟩ := rfl
example : sampleNot.1.1.2 (.inr true) = ⟨1, (1 : Fin 3)⟩ := rfl

end LargeIRTest
