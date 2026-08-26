/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.FamBoundary

/-!
# Tests for the boundary of the free coproduct completion in presheaves

The two brackets on membership: a representable times a set is a family
presheaf, and the terminal presheaf is one exactly when the base supplies the
terminal object it would have to represent.

## Tags

prototype, presheaf, free coproduct completion, reduction test
-/

set_option linter.privateModule false

open CategoryTheory CategoryTheory.Limits GebProto.FamBoundary

/-! ## The walking parallel pair -/

/-- The two parallel morphisms are distinct, so `one` is not terminal. -/
theorem oneNotTerminal :
    (WalkingParallelPairHom.left : WalkingParallelPair.zero ⟶ WalkingParallelPair.one)
      ≠ WalkingParallelPairHom.right :=
  left_ne_right

/-- Nothing maps from `one` to `zero`, so `zero` is not terminal either. -/
theorem zeroNotTerminal :
    IsEmpty (WalkingParallelPair.one ⟶ WalkingParallelPair.zero) :=
  isEmpty_one_to_zero

/-- With no terminal object, the terminal presheaf is outside the free coproduct
completion. -/
theorem topNotFam : ¬ IsFamPsh (topPsh WalkingParallelPair) :=
  not_isFamPsh_topPsh

/-! ## A base that does supply one

`WalkingParallelPair` with only the identities — the discrete category on it —
would; so does any base with a terminal object, `PUnit` being the smallest. -/

/-- Over the one-object base the terminal presheaf is a family presheaf. -/
theorem topFamOverPUnit : IsFamPsh (topPsh (Discrete PUnit)) :=
  isFamPsh_topPsh_of_terminal ⟨PUnit.unit⟩
    fun c ↦ ⟨⟨Discrete.eqToHom (by subsingleton)⟩, fun f ↦ by subsingleton⟩

/-! ## Universal elements

Genericity is not stable under arbitrary morphisms of families: over the walking
parallel pair, the morphism carrying the code decoding to `zero` onto the one
decoding to `one` sends the universal element to a non-universal one. -/

/-- The morphism of families that moves the universal element. -/
def moveUniversal :
    FamMor PUnit (fun _ ↦ WalkingParallelPair.zero) PUnit
      (fun _ ↦ WalkingParallelPair.one) where
  code := id
  dec _ := WalkingParallelPairHom.left

/-- It does not preserve universal elements. -/
theorem not_preservesGeneric_moveUniversal : ¬ PreservesUniversalElement moveUniversal := by
  rintro h
  obtain ⟨h₀, -⟩ := h PUnit.unit
  exact WalkingParallelPair.noConfusion h₀

/-- The universal element it moves. -/
def universalZero :
    (famPsh PUnit (fun _ ↦ WalkingParallelPair.zero)).obj ⟨WalkingParallelPair.zero⟩ :=
  universalElement PUnit (fun _ ↦ WalkingParallelPair.zero) PUnit.unit

theorem isUniversalElement_universalZero : IsUniversalElement universalZero :=
  ⟨rfl, rfl⟩

/-- Its image is not universal: the two objects differ. -/
theorem not_isUniversalElement_image :
    ¬ IsUniversalElement (famMorApp moveUniversal universalZero) := by
  rintro ⟨h₀, -⟩
  exact WalkingParallelPair.noConfusion h₀

/-! ## The p.r.a. formula's value

Whatever the multiplicities, the value is a family presheaf: the multiplicity
lands in the code type. -/

/-- A two-element multiplicity at every shape is no obstruction. -/
theorem praFamDoubled : IsFamPsh (praPsh (C := Discrete PUnit) PUnit (fun _ ↦ ⟨PUnit.unit⟩)
    (fun _ ↦ Bool)) :=
  isFamPsh_praPsh _ _ _
