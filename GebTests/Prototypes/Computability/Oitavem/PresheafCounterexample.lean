/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.PresheafCounterexample -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.PresheafCounterexample -- shake: keep
public import Geb.Prototypes.Computability.PresheafScan -- shake: keep
public meta import Geb.Prototypes.Computability.PresheafScan -- shake: keep

set_option doc.verso true in
/-!
# Executable checks for the presheaf counterexample

Check that the native checker follows a predicate's verdict on valid slice
trees, and that unary expressions can be decoded from their syntax codes.

## Main definitions

* {lit}`scanned` exercises the decomposition into node tests.
* {lit}`leafComparison` exercises restriction along the nonidentity morphism.

## Tags

presheaf, W-type, hereditary naturality, diagonalization
-/

set_option doc.verso true

namespace Geb.Oitavem.PresheafCounterexample.Tests

open CategoryTheory Geb.PresheafRecognition
open scoped FinEnum

#guard nativeCheck (fun _ ↦ true) (testTree (fun _ ↦ true) [false]).1
#guard !nativeCheck (fun _ ↦ false) (testTree (fun _ ↦ false) [true]).1
#guard ([[], [true], [false], [true, false]] : List (List Bool)).all fun w ↦
  nativeCheck (List.headD · false) (testTree (List.headD · false) w).1 == w.headD false

#guard (readExpr (syntaxCode.spell (Expr.initial (.proj 1 0)).1.1)).isSome
#guard diagonal testWord (syntaxCode.spell (Expr.initial (.zero 1)).1.1)

/-- The local scan on the counterexample family. -/
@[expose] public def scanned (p : List Bool → Bool) (w : List Bool) : Bool :=
  (occurrences (presheafFinitary p) (testTree p w).1).all
    (localNaturality (presheaf p) inferInstance inferInstance homEnum
      (presheafFinitary p) (treeDecidableEq p))

#guard scanned (fun _ ↦ true) [false]
#guard !scanned (fun _ ↦ false) [true]

/-- Compare the nonidentity restriction of a dependent leaf with a base leaf. -/
@[expose] public def leafComparison (b : Bool) : Bool :=
  restrictedEq (presheaf (fun _ ↦ false)) (shapeDecidableEq _) (presheafFinitary _)
    (fun t u ↦ (treeDecidableEq _ t u).decide) PresheafPFunctor.arrow
    (baseLeaf (fun _ ↦ false) b).1 (dependentLeaf (fun _ ↦ false)).1 rfl

#guard leafComparison true
#guard !leafComparison false
#guard restrictedEq (presheaf (fun _ ↦ false)) (shapeDecidableEq _) (presheafFinitary _)
  (fun t u ↦ (treeDecidableEq _ t u).decide) (𝟙 (1 : Fin 2))
  (testTree (fun _ ↦ false) [true]).1 (testTree (fun _ ↦ false) [true]).1 rfl

end Geb.Oitavem.PresheafCounterexample.Tests
