/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LargeIR.Product -- shake: keep

/-!
# Tests for the walking arrow over an index type

Exercises `Geb.Prototypes.LargeIR.Product` on the slice polynomial endofunctor
of alternating lists over `Bool`: at each index a `nil` with no directions and
a `cons` with one direction at the other index. Its slice W-type is the
alternating chains, and the tests read two of them, the empty chain at `true`
and the chain of one step at `false`, through the fixed-point isomorphism into
the transcription's value at the W-type's presheaf: the shapes, the base
which is a point, and the level-`1` assignment, which is the child chain.

## Tags

prototype, presheaf, walking arrow, slice polynomial functor, W-type,
reduction test
-/

@[expose] public section

open CategoryTheory GebProto.LargeIR.Product

namespace LargeIRTest

/-- The directions of the alternating-list endofunctor: none for `nil`, one
for `cons`. -/
def altDir : Bool ⊕ Bool → Type
  | .inl _ => PEmpty
  | .inr _ => Unit

/-- The alternating-list endofunctor of `Type/Bool`: `nil` and `cons` at each
index, the child of a `cons` at the other index. -/
def altList : SlicePFunctor.{0, 0, 0, 0} Bool Bool where
  toPFunctor := ⟨Bool ⊕ Bool, altDir⟩
  r := fun d ↦
    match d with
    | ⟨.inl _, e⟩ => PEmpty.elim e
    | ⟨.inr x, _⟩ => !x
  q := Sum.elim id id

/-- The empty chain at `true`. -/
def nilT : altList.W :=
  SlicePFunctor.W.mk ⟨⟨.inl true, fun e ↦ PEmpty.elim e⟩, funext fun e ↦ PEmpty.elim e⟩

/-- The chain of one step at `false`, whose child is the empty chain at `true`. -/
def consF : altList.W :=
  SlicePFunctor.W.mk ⟨⟨.inr false, fun _ ↦ nilT⟩, funext fun _ ↦ rfl⟩

-- The chains lie over their indices.
example : altList.wIndex nilT = true := rfl
example : altList.wIndex consF = false := rfl

-- The W-type's presheaf has a point at level `0` and the chains over an index
-- at level `1`.
example : (wPsh altList).obj ⟨mkIdx 0 true⟩ = Unit := rfl
example : (wPsh altList).obj ⟨mkIdx 1 true⟩ = { z : altList.W // altList.wIndex z = true } := rfl

/-- The one-step chain read through the fixed-point isomorphism as an element
of the transcription's value at the W-type's presheaf. -/
def consElem : (prodPsh altList).obj (wPsh altList) :=
  ((wFixed altList false).symm ⟨consF, rfl⟩).1

-- Its shape is the `cons` at `false`.
example : consElem.shape = .inr (.inr false) := rfl

-- Its level-`1` assignment at the one direction, at index `true`, is the
-- child chain.
example : ((elemEquiv (wPsh altList) (prodPsh altList) consElem).2.2 true ⟨.inr (), rfl⟩).1.1 =
    nilT :=
  rfl

-- The empty chain reads as the `nil` at `true`.
example : (((wFixed altList true).symm ⟨nilT, rfl⟩).1).shape = .inr (.inl true) := rfl

-- The fixed-point isomorphism inverts.
example : wFixed altList false ((wFixed altList false).symm ⟨consF, rfl⟩) = ⟨consF, rfl⟩ :=
  (wFixed altList false).apply_symm_apply _

-- The base is a point.
example : levelZeroEquiv altList altList.wIndex true
    ((levelZeroEquiv altList altList.wIndex true).symm ()) = () :=
  rfl

end LargeIRTest
