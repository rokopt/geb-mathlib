/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.FinCardUniverse.Basic

/-!
# Tests for the universe endofunctor over a non-discrete base

Reduction tests for the base category, the two type formers, and the arities,
and the check that the dependent-sum and dependent-product universes differ only
in their shape-output map.

## Tags

prototype, presheaf, universe, parametric right adjoint, reduction test
-/

set_option linter.privateModule false

open CategoryTheory GebProto.FinCardUniverse

/-! ## The base category

Composition is function composition, so the category laws hold definitionally.
This is what the construction runs on and what the `FinSetSkel` seal would
block. -/

example (X Y Z W : Card) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := rfl

example (X Y : Card) (f : X ⟶ Y) : 𝟙 X ≫ f = f := rfl

example (X Y : Card) (f : X ⟶ Y) : f ≫ 𝟙 Y = f := rfl

/-- The base is not discrete: there is a morphism between distinct objects. -/
def emptyToOne : (⟨0⟩ : Card) ⟶ ⟨1⟩ := fun i ↦ i.elim0

example : (⟨0⟩ : Card) ≠ ⟨1⟩ := by decide

/-! ## The type formers

The formers compute the cardinalities of the dependent sum and the dependent
product. -/

example : sigmaFormer ⟨2⟩ (fun _ ↦ ⟨3⟩) = ⟨6⟩ := rfl
example : piFormer ⟨2⟩ (fun _ ↦ ⟨3⟩) = ⟨9⟩ := rfl
example : sigmaFormer ⟨0⟩ (fun i ↦ i.elim0) = ⟨0⟩ := rfl
example : piFormer ⟨0⟩ (fun i ↦ i.elim0) = ⟨1⟩ := rfl

/-! ## Codes and arities -/

example : out sigmaFormer (.iota ⟨2⟩) = ⟨2⟩ := rfl
example : bound (.bind ⟨2⟩ (fun _ ↦ ⟨3⟩)) (.inl ()) = ⟨2⟩ := rfl
example : bound (.bind ⟨2⟩ (fun _ ↦ ⟨3⟩)) (.inr ⟨1, Nat.one_lt_two⟩) = ⟨3⟩ := rfl

/-- The `iota` codes are leaves: they have no generic directions. -/
theorem idxIotaEmpty (c : Card) : IsEmpty (Idx (.iota c)) := inferInstanceAs (IsEmpty Empty)

/-- The two universes have the same arities at corresponding shapes: the type
former enters only through the object a shape lies over, which is the
shape-output map `q`. -/
theorem dirIndependentOfFormer (c : Code) (j : Card) (φ : j ⟶ out sigmaFormer c)
    (ψ : j ⟶ out piFormer c) :
    Dir (⟨c, j, φ⟩ : Shp sigmaFormer) = Dir (⟨c, j, ψ⟩ : Shp piFormer) := rfl
