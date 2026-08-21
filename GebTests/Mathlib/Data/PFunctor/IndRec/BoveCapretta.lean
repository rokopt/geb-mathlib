/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.BoveCapretta

/-!
# Tests for the Bove-Capretta domain of a call-by-value evaluator

`rfl` tests reading the domain code back out as node types, checking the
de Bruijn operations, and evaluating terms whose evidence exercises both
branches of the application case.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

indexed induction-recursion, Bove-Capretta, lambda calculus
-/

@[expose] public section

open CategoryTheory IndRec IndRec.BoveCapretta

/-- The decoding family of the domain code: every index decodes to a
term. -/
@[reducible] def testCbvDec : Tm → Type := fun _ ↦ Tm

-- A value needs no recursive evidence, only the proof that it is the
-- term being evaluated.
example (G : IIR.FamSlice.{0, 0} Tm testCbvDec) (t n : Tm) :
    (IIR.interp Tm testCbvDec Tm testCbvDec (branch (tmLam t)) G n).1 =
      ULift (PLift (tmLam t = n)) :=
  rfl

-- An application node holds evidence for the function part, and then
-- evidence whose shape is chosen by that part's value.
example (G : IIR.FamSlice.{0, 0} Tm testCbvDec) (f a n : Tm) :
    (IIR.interp Tm testCbvDec Tm testCbvDec (branch (tmApp f a)) G n).1 =
      Σ ig : PUnit.{1} → (G f).1,
        (IIR.interp Tm testCbvDec Tm testCbvDec
          (appBranch (tmApp f a) a ((G f).2 (ig PUnit.unit))) G n).1 :=
  rfl

-- When the function part evaluates to an abstraction, the node
-- continues with evidence for the argument and then for the substituted
-- body, at an index built from the argument's value.
example (G : IIR.FamSlice.{0, 0} Tm testCbvDec) (t a b n : Tm) :
    (IIR.interp Tm testCbvDec Tm testCbvDec (appBranch t a (tmLam b)) G n).1 =
      Σ jg : PUnit.{1} → (G a).1,
        Σ _ : PUnit.{1} → (G (subst0 ((G a).2 (jg PUnit.unit)) b)).1,
          ULift (PLift (t = n)) :=
  rfl

-- Shifting raises a free variable and leaves a bound one alone.
example : tmShift 0 (tmVar 0) = tmVar 1 := rfl

example : tmShift 1 (tmLam (tmVar 0)) = tmLam (tmVar 0) := rfl

-- Substituting for variable `0` decrements the free variables above it.
example : subst0 (tmVar 5) (tmApp (tmVar 0) (tmVar 1)) = tmApp (tmVar 5) (tmVar 0) := rfl

/-- The identity applied to a free variable. -/
def testCbvIdVar : Tm := tmApp (tmLam (tmVar 0)) (tmVar 0)

/-- The evidence that the evaluator terminates on `testCbvIdVar`: the
function part, the argument, and the substituted body, which is the
argument again. -/
def testCbvIdVarEvidence : Dom testCbvIdVar :=
  ⟨IR.W.mk (Σ _ : Tm, Tm) irCode
      ⟨testCbvIdVar,
        fun _ ↦ lamMu (tmVar 0), ULift.up (PLift.up fun _ ↦ rfl),
        fun _ ↦ varMu 0, ULift.up (PLift.up fun _ ↦ rfl),
        fun _ ↦ varMu 0, ULift.up (PLift.up fun _ ↦ rfl),
        ULift.up ()⟩,
    rfl⟩

-- The beta-redex evaluates to its argument.
example : eval testCbvIdVar testCbvIdVarEvidence = tmVar 0 := rfl

/-- A neutral application, whose function part is not an abstraction. -/
def testCbvNeutral : Tm := tmApp (tmVar 0) (tmVar 1)

/-- The evidence that the evaluator terminates on `testCbvNeutral`: the
function part and the argument, and no third field, since the
non-abstraction branch of the application case stops there. -/
def testCbvNeutralEvidence : Dom testCbvNeutral :=
  ⟨IR.W.mk (Σ _ : Tm, Tm) irCode
      ⟨testCbvNeutral,
        fun _ ↦ varMu 0, ULift.up (PLift.up fun _ ↦ rfl),
        fun _ ↦ varMu 1, ULift.up (PLift.up fun _ ↦ rfl),
        ULift.up ()⟩,
    rfl⟩

-- The neutral application evaluates to the application of the two
-- values.
example : eval testCbvNeutral testCbvNeutralEvidence = tmApp (tmVar 0) (tmVar 1) := rfl
