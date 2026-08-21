/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Language

/-!
# Tests for the language of sums and products

`rfl` tests reading the code of each node form back out as a node type
and a decoding, and evaluating expressions built from the constructors.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

inductive-recursive, sum, product
-/

@[expose] public section

open CategoryTheory IndRec

/-- An arbitrary object of `Type/ℕ` at which to read the codes of the
node forms. -/
def testLangObj (X : Type) (d : X → Nat) : FreeCoprodCompDisc.{0, 0} Nat := ⟨X, d⟩

-- A literal node carries a natural number, and decodes to it.
example (X : Type) (d : X → Nat) :
    (IR.interpObj Nat Nat (Language.tagCode .lit) (testLangObj X d)).1 =
      Σ _ : Nat, ULift Unit :=
  rfl

example (X : Type) (d : X → Nat) (n : Nat) :
    (IR.interpObj Nat Nat (Language.tagCode .lit) (testLangObj X d)).2
        ⟨n, ULift.up ()⟩ = n :=
  rfl

-- A sum node carries one recursive field, its bound, and then a family
-- of recursive fields indexed by `Fin` of the bound's decoded value.
example (X : Type) (d : X → Nat) :
    (IR.interpObj Nat Nat (Language.tagCode .sum) (testLangObj X d)).1 =
      Σ g : PUnit.{1} → X, Σ _ : Fin (d (g PUnit.unit)) → X, ULift Unit :=
  rfl

example (X : Type) (d : X → Nat) (g : PUnit.{1} → X)
    (h : Fin (d (g PUnit.unit)) → X) :
    (IR.interpObj Nat Nat (Language.tagCode .sum) (testLangObj X d)).2
        ⟨g, h, ULift.up ()⟩ = (List.ofFn fun i ↦ d (h i)).sum :=
  rfl

-- A product node has the same shape, and decodes to the product.
example (X : Type) (d : X → Nat) :
    (IR.interpObj Nat Nat (Language.tagCode .prod) (testLangObj X d)).1 =
      Σ g : PUnit.{1} → X, Σ _ : Fin (d (g PUnit.unit)) → X, ULift Unit :=
  rfl

example (X : Type) (d : X → Nat) (g : PUnit.{1} → X)
    (h : Fin (d (g PUnit.unit)) → X) :
    (IR.interpObj Nat Nat (Language.tagCode .prod) (testLangObj X d)).2
        ⟨g, h, ULift.up ()⟩ = (List.ofFn fun i ↦ d (h i)).prod :=
  rfl

/-- The product of the first three positive integers, as an expression of
the language: the summand family's index is coerced to a literal one
greater than itself. -/
def testLangFactorial : Language.Expr :=
  Language.prod (Language.lit 3) fun n ↦ Language.lit (n.val + 1)

-- The expression decodes to `6`.
example : Language.value testLangFactorial = 6 := rfl

/-- A nested expression: the sum, over `Fin` of the value of the paper's
example, of the constant `2`. -/
def testLangNested : Language.Expr :=
  Language.sum Language.sumFirstFive fun _ ↦ Language.lit 2

-- The nested expression decodes to `20`.
example : Language.value testLangNested = 20 := rfl
