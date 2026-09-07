/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.UniverseVariance.Retract

/-!
# Tests for the two type formers' preservation of retraction

A `Split` on the bound object together with a `Split` at each index of the
binder's family, and the two formers' actions computed at it. The family
upstairs is not the reindexing of the one downstairs, which is the case the
formers' actions on a morphism of families present.

## Tags

prototype, universe, variance, split epimorphism, retract, reduction test
-/

set_option linter.privateModule false

open GebProto.UniverseVariance

/-! ## A pair of splits, neither invertible -/

/-- The map from the booleans to the singleton, with `true` as its section. -/
def boolToUnit : Split Bool Unit where
  toFun _ := ()
  sect _ := true
  toFun_sect _ := rfl

/-- The map from the naturals to the booleans testing equality with one, with
the two values it distinguishes as its section. -/
def natToBool : Split Nat Bool where
  toFun n := n == 1
  sect b := cond b 1 0
  toFun_sect b := by cases b <;> rfl

/-- The dependent-sum former's action on the pair. -/
def sigmaSplitExample : Split (Σ _ : Bool, Nat) (Σ _ : Unit, Bool) :=
  sigmaSplit boolToUnit fun _ ↦ natToBool

/-- The dependent-product former's action on the pair. -/
def piSplitExample : Split ((_ : Bool) → Nat) ((_ : Unit) → Bool) :=
  piSplit boolToUnit fun _ ↦ natToBool

/-! ## The two actions compute

The dependent-sum former's function pushes both components forward; its section
pairs the two sections. The dependent-product former's function evaluates at the
section on the bound object; its section is defined at every element of the
bound object upstairs, including the one outside the image of the section. -/

example : sigmaSplitExample.toFun ⟨true, 1⟩ = ⟨(), true⟩ := rfl

example : sigmaSplitExample.sect ⟨(), true⟩ = ⟨true, 1⟩ := rfl

example : sigmaSplitExample.sect ⟨(), false⟩ = ⟨true, 0⟩ := rfl

example : piSplitExample.toFun (fun _ ↦ 1) () = true := rfl

example : piSplitExample.sect (fun _ ↦ true) false = 1 := rfl

example : piSplitExample.sect (fun _ ↦ true) true = 1 := rfl

/-! ## The identity laws

The composition laws are exercised at a morphism of families in
`GebTests/Prototypes/UniverseVariance/Universe.lean`. -/

example (X : Type) (Y : X → Type) :
    sigmaSplit (Split.id X) (fun x ↦ Split.id (Y x)) = Split.id (Σ x, Y x) :=
  sigmaSplit_id Y

example (X : Type) (Y : X → Type) :
    piSplit (Split.id X) (fun x ↦ Split.id (Y x)) = Split.id ((x : X) → Y x) :=
  piSplit_id Y
