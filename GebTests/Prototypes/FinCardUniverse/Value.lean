/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.FinCardUniverse.Value

/-!
# Tests for the value of the universe endofunctor over a non-discrete base

The two things the value computation shows: a binder shape accepts a bound code
whose decoding differs from the object the shape declares, and the object the
resulting code decodes to is fixed by that declaration rather than by the code
bound. Together with the reduction tests for Example 3.6 of
[GhaniNordvallForsbergMalatesta2015].

## Tags

prototype, presheaf, universe, reduction test
-/

set_option linter.privateModule false

open CategoryTheory GebProto.FinCardUniverse

/-! ## The declared decoding is not the bound code's decoding -/

-- The bound code denotes the singleton where the shape declares the empty
-- object.
example : oneFam (junkArity (.inl ())).1 = ⟨1⟩ := rfl
example : bound emptyBindCode (.inl ()) = ⟨0⟩ := rfl
example : oneFam (junkArity (.inl ())).1 ≠ bound emptyBindCode (.inl ()) := by decide

-- The element of the functor's value it gives has that shape.
example : junkObj.shape = junkShape := rfl

-- And the shape's output object, which is the code's decoding, is fixed by the
-- declaration.
example : (universeFunctor sigmaFormer).q junkObj.shape = ⟨0⟩ := rfl

/-! ## The decoding does not depend on the code bound

A second family, with one code denoting the singleton and one the empty object,
supplies two arity homs for the same shape whose bound codes decode
differently. -/

/-- A family with two codes, denoting the singleton and the empty object. -/
def twoFam : Bool → Card := fun b ↦ if b then ⟨1⟩ else ⟨0⟩

/-- For each code of `twoFam`, an arity hom for `junkShape` binding it: the
generic direction asks only for a morphism out of the declared empty object. -/
def bindArity (b : Bool) :
    (k : Idx emptyBindCode) → Σ u : Bool, (bound emptyBindCode k ⟶ twoFam u)
  | .inl _ => ⟨b, fun i ↦ i.elim0⟩
  | .inr s => s.elim0

/-- The two bound codes decode differently. -/
example : twoFam (bindArity true (.inl ())).1 ≠ twoFam (bindArity false (.inl ())).1 := by
  decide

/-- The shape is the same in both cases, so the object the resulting code
decodes to is too. -/
example : out sigmaFormer emptyBindCode = ⟨0⟩ := rfl

/-! ## Example 3.6 at this scale

The empty dependent product is the singleton, and the dependent product of the
counterexample family is empty, so the covariant action the dependent-product
former would need is a map from the singleton to the empty object. -/

example : piFormer ⟨0⟩ counterFamReindexed = ⟨1⟩ := rfl
example : piFormer ⟨1⟩ counterFam = ⟨0⟩ := rfl
example : sigmaFormer ⟨0⟩ counterFamReindexed = ⟨0⟩ := rfl
example : sigmaFormer ⟨1⟩ counterFam = ⟨0⟩ := rfl

/-- The obstruction, as a decidable statement about the base: no morphism from
the singleton to the empty object. -/
theorem noOneToEmpty : IsEmpty ((⟨1⟩ : Card) ⟶ ⟨0⟩) := piFormer_not_covariant
