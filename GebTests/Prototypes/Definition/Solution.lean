/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Solution -- shake: keep
public import GebTests.Prototypes.Definition.Basic -- shake: keep

public meta import Geb.Prototypes.Definition.Solution -- shake: keep
public meta import GebTests.Prototypes.Definition.Basic -- shake: keep

set_option doc.verso true in
/-!
# Examples of equations that are definitions

A derived operation evaluates as its expansion does. A well-founded block of three exports,
each body referring only to earlier exports, has exactly one solution; the unguarded alias
block of the basic examples has every interpretation as a solution.

## Main definitions

* {lit}`chain` imports a value and exports it, its double, and the sum of the two.
* {lit}`chainValues` is the interpretation of {lit}`chain` for an import of seven.

## Main statements

* {lit}`chainValues_solution` verifies that interpretation.
* {lit}`chain_solution_unique` derives from well-foundedness that it is the only one.

## Tags

definition, definitional extension, well-founded recursion, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.SolutionTests

open PFunctor Geb.Definition.Tests

/-- Each export's body refers to the import and to exports of smaller index. -/
def chain : WFBlock arithmetic Unit fun j i : Fin 3 ↦ j.val < i.val := fun i ↦
  match i with
  | 0 => .pure (.inl ())
  | 1 => add (.pure (.inr ⟨0, Nat.zero_lt_one⟩)) (.pure (.inr ⟨0, Nat.zero_lt_one⟩))
  | 2 => add (.pure (.inr ⟨1, Nat.one_lt_two⟩)) (.pure (.inr ⟨0, Nat.zero_lt_two⟩))

/-- Seven, fourteen and twenty-one. -/
def chainValues (i : Fin 3) : ℕ := 7 * (i.val + 1)

/-- The block's interpretation for an import of seven. -/
theorem chainValues_solution :
    IsSolution arithmeticAlg (fun _ ↦ 7) chain.toBlock chainValues := by
  intro i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

/-- Well-foundedness makes that interpretation the only solution. -/
theorem chain_solution_unique (v : Fin 3 → ℕ)
    (h : IsSolution arithmeticAlg (fun _ ↦ 7) chain.toBlock v) : v = chainValues :=
  (WFBlock.existsUnique_isSolution (measure Fin.val).wf arithmeticAlg (fun _ ↦ 7) chain).unique
    h chainValues_solution

-- The derived doubling evaluates as its expansion does.
#guard eval (derivedAlg arithmeticAlg double) (fun _ : Unit ↦ 8)
  (.liftBind () fun _ ↦ .pure ()) = 16

end Geb.Definition.SolutionTests

end
