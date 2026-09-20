/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem -- shake: keep; executable checks
public meta import Geb.Prototypes.Computability.Oitavem -- shake: keep; executable checks

set_option doc.verso true in
/-!
# Executable checks for Logs

Check the compiled evaluator on numerical and string primitives, leading zeroes,
log-transition, safe recursion, concatenation recursion, and quadratic output.
The raw syntax validator rejects an attempt to substitute a safe function into
a normal argument slot.

## Main definitions

* {lit}`complement`, {lit}`boundedCounter`, and {lit}`squareCap` exercise the closure schemes.
* {lit}`invalidRaw` supplies a tree with an inadmissible child arity.

## Tags

logspace, executable checks, function algebra
-/

set_option doc.verso true

namespace Geb.Oitavem.Tests

open Geb.Oitavem
open scoped FinEnum

#guard (List.range 40).all fun n ↦ rank (unrank n) == n
#guard ([[], [false], [true], [false, false], [true, false], [false, true], [true, true]] :
  List (List Bool)).map rank == List.range 7
#guard Initial.eval .iterPred ![[true, true], [false, true, false]] == [false]
#guard Initial.eval .numericSub ![unrank 3, unrank 9] == unrank 6
#guard Initial.eval .numericSub ![unrank 9, unrank 3] == []
#guard Initial.eval .last ![[]] == [false]
#guard Initial.eval .cond ![[], [true], [false]] == [true]
#guard Initial.eval .cond ![[false], [true], [false]] == [false]

#guard (List.range 20).all fun n ↦
  lengthByRec.eval ![List.replicate n false] Fin.elim0 == unrank n
#guard squareWord.eval ![[true, false, false]] Fin.elim0 ==
  [true, false, false, true, false, false, true, false, false]

/-- The complement of each input digit, using concatenation recursion. -/
@[expose] public def complement : Expr 1 0 :=
  Expr.concatRec (Expr.initial (.zero 0)) fun b ↦
    Expr.comp (safe := false) (Expr.initial (.succ (!b))) ![Expr.initial (.zero 1)]

#guard complement.eval ![[false, true, false]] Fin.elim0 == [true, false, true]

/-- Increment the recursive value after capping it at one, so it stabilizes at two. -/
@[expose] public def boundedCounter : Expr 1 0 :=
  Expr.boundedRec (Expr.initial (.zero 0))
    (fun _ ↦ Expr.comp (safe := false) (Expr.initial .numericSucc)
      ![Expr.initial (.proj 2 0)])
    (Expr.comp (safe := false) (Expr.initial (.succ false)) ![Expr.initial (.zero 1)])

#guard (List.range 8).all fun n ↦
  boundedCounter.eval ![List.replicate n false] Fin.elim0 == unrank (min n 2)

/-- Promote a safe value capped by the square of the normal input's length. -/
@[expose] public def squareCap : Expr 1 1 :=
  Expr.comp (safe := true) (Expr.logTransition (Expr.initial (.proj 1 0)))
    ![squareWord, Expr.initial (.zero 1)]

#guard squareCap.truncationBound.eval ![[true, false]] Fin.elim0 ==
  [true, false, true, false]
#guard squareCap.eval ![[true, false]] ![unrank 200] == unrank 4
#guard (Expr.logTransition (Expr.initial (.proj 1 0))).eval
  ![[false, false], unrank 4] ![unrank 20] == unrank 6
#guard (Expr.logTransition (Expr.initial (.proj 1 0))).eval
  ![[false, false], unrank 4] ![unrank 1] == unrank 5
#guard (List.range 20).all fun n ↦ cappedRank 4 (unrank n) == min n 4
#guard (List.range 20).all fun B ↦ (List.range 40).all fun n ↦
  cappedRank B ((unrank n).take B.size) == min n B
#guard (List.range 10).all fun n ↦
  prefixLoop 2 (fun (_ : Fin 0 → List Bool) _ ↦ [])
    (fun _ _ y ↦ unrank (min (rank (y 0)) 1 + 1))
    (List.replicate n false) Fin.elim0 n == unrank (min n 2)

/-- A composition with a safe function in a normal argument slot. -/
@[expose] public def invalidRaw : sig.toPFunctor.W :=
  WType.mk (.comp 2 1 false) fun d ↦ match d with
    | .inl () => (Expr.initial (.proj 1 0)).1.1
    | .inr _ => (Expr.logTransition (Expr.initial (.proj 1 0))).1.1

#guard !wellFormed invalidRaw
#guard wellFormed lengthByRec.1.1

end Geb.Oitavem.Tests
