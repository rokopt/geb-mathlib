/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.UniverseVariance.Basic

/-!
# Tests for the variance of the universe's type formers

The two ends of the claim that split epimorphisms sit strictly between the
isomorphisms and all functions: every equivalence is split (`Split.ofEquiv`),
and a split epimorphism need not be injective (`notInjective_boolToUnit`),
while `not_piMap` rules out all functions. Together with reduction tests for
the two formers' actions.

## Tags

prototype, universe, variance, split epimorphism, reduction test
-/

set_option linter.privateModule false

open GebProto.UniverseVariance

/-! ## A split epimorphism that is not an isomorphism -/

/-- The map from the booleans to the singleton, with `true` as its section. -/
def boolToUnit : Split Bool Unit where
  toFun _ := ()
  sect _ := true
  toFun_sect _ := rfl

/-- It is not injective, so it is not an isomorphism: the class of morphisms the
dependent-product former is functorial along is strictly larger than the
groupoid. -/
theorem notInjective_boolToUnit : ¬ Function.Injective boolToUnit.toFun :=
  fun h ↦ absurd (@h true false rfl) (by decide)

/-- Every equivalence is split, so the groupoid is contained in the class. -/
def splitOfRefl (A : Type) : Split A A := Split.ofEquiv (Equiv.refl A)

example : (splitOfRefl Bool).toFun true = true := rfl

/-! ## The two formers' actions compute -/

-- The dependent-product former's action evaluates the section family at the
-- chosen section.
example : piMap boolToUnit (fun _ ↦ Nat) (fun b ↦ cond b 1 2) () = 1 := rfl

-- The dependent-sum former's action pushes the index forward.
example : sigmaMap (fun _ : Bool ↦ ()) (fun _ ↦ Nat) ⟨true, 5⟩ = ⟨(), 5⟩ := rfl

/-! ## The composition laws -/

example (e : Split Bool Unit) (Y : Unit → Type) :
    piMap (e.comp (Split.id Unit)) Y = piMap e Y :=
  rfl

example (X : Type) (Y : X → Type) : piMap (Split.id X) Y = id := piMap_id Y
