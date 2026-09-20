/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.PresheafCounterexample -- shake: keep
public meta import Geb.Prototypes.Computability.Oitavem.PresheafCounterexample -- shake: keep

set_option doc.verso true in
/-!
# Executable checks for the presheaf counterexample

Check that the native checker follows a predicate's verdict on valid slice
trees, and that unary expressions can be decoded from their syntax codes.

## Tags

presheaf, W-type, hereditary naturality, diagonalization
-/

set_option doc.verso true

namespace Geb.Oitavem.PresheafCounterexample.Tests

#guard nativeCheck (fun _ ↦ true) (testTree (fun _ ↦ true) [false]).1
#guard !nativeCheck (fun _ ↦ false) (testTree (fun _ ↦ false) [true]).1
#guard ([[], [true], [false], [true, false]] : List (List Bool)).all fun w ↦
  nativeCheck (List.headD · false) (testTree (List.headD · false) w).1 == w.headD false

#guard (readExpr (syntaxCode.spell (Expr.initial (.proj 1 0)).1.1)).isSome
#guard diagonal testWord (syntaxCode.spell (Expr.initial (.zero 1)).1.1)

end Geb.Oitavem.PresheafCounterexample.Tests
