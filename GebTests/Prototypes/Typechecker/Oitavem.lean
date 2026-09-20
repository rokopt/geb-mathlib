/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Typechecker.Oitavem -- shake: keep
public meta import Geb.Prototypes.Typechecker.Oitavem -- shake: keep

set_option doc.verso true in
/-!
# Oitavem decision-problem checks

Exercise the bounded scan on empty input, failures inside a word, and a test
that reads the unchanged input. Check composition order and the growth of the
fold whose constructor algebra is admissible but whose eliminator is not.

## Main definitions

* {lit}`headTrue` supplies the local test for a word containing only true bits.

## Tags

logspace, typechecker, scan, fold
-/

set_option doc.verso true

namespace Geb.Oitavem.Tests

/-- Accept the empty suffix, or a suffix whose head is true. -/
@[expose] public def headTrue : Expr 2 0 :=
  Expr.comp (safe := false) (Expr.initial .cond)
    ![Expr.initial (.proj 2 0), Expr.const 2 [true],
      Expr.comp (safe := false) (Expr.initial .numericPred)
        ![Expr.comp (safe := false) (Expr.initial .last) ![Expr.initial (.proj 2 0)]]]

#guard headTrue.scanProblem.checker.val [] == [true]
#guard headTrue.scanProblem.checker.val [true, true, true] == [true]
#guard headTrue.scanProblem.checker.val [true, false, true] == []
#guard headTrue.scanProblem.checker.val [false, true] == []
#guard headTrue.scanProblem.checker.val [true, false] == []
#guard (Expr.initial (.proj 2 1)).scan.unary [false] == [true]
#guard (Expr.initial (.proj 2 1)).scan.unary [] == []
#guard (Expr.initial (.proj 2 0)).scan.unary [true] == []
#guard ((Expr.initial (.succ true)).admissible *
  (Expr.initial (.succ false)).admissible).val [] == [true, false]
#guard ([[], [false], [true, false]] : List (List Bool)).map
  (fun w ↦ (squareFold w).length) == [2, 4, 16]

end Geb.Oitavem.Tests
