/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Metalogic -- shake: keep
public meta import Geb.Prototypes.Metalogic -- shake: keep

set_option doc.verso true in
/-!
# The first rung of the metalogic

Certificates checked by {name}`Geb.Metalogic.check`: a theorem with a hypothesis, derived by
congruence; a substitution, instantiating a variable of a derived equation; and an induction,
proving that appending the empty list to a list, written with the kernel's right fold, gives
the list. Certificates with an altered binder, an invalid dependency or a false conclusion do
not check to that conclusion.

## Main definitions

* {lit}`arr`, {lit}`lt` — the types of functions on trees and of lists of trees.
* {lit}`g`, {lit}`appendNil` — the step of appending and the append of the empty list.
* {lit}`step`, {lit}`induction` — the certificate of the inductive step and of the theorem.

## Tags

bootstrap, metalogic, proof certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Metalogic.Tests

open Geb.Kernel

/-- The type of functions on trees. -/
def arr : Tree := tArrow tT tT

/-- The type of lists of trees. -/
def lt : Tree := tList tT

/-- The step of appending: a tree and a list to the list with the tree in front. -/
def g : Tree := mk 9 [tT, mk 9 [lt, mk 20 [Tm.var 1, Tm.var 0]]]

/-- The right fold of lists of trees at lists of trees. -/
def foldrL : Tree := mk 21 [tT, lt]

/-- The empty list of trees. -/
def nilT : Tree := mk 19 [tT]

/-- The list of the innermost variable with the empty list appended. -/
def appendNil : Tree := apps foldrL [g, nilT, Tm.var 0]

/-- The inductive step, in the context of a tail and a head: the append of the head in front of
the tail is the head in front of the append of the tail, by the fold's computation and two β
steps, and that is the head in front of the tail by the hypothesis. -/
def step : Tree :=
  let r := appendNil
  let body1 := mk 9 [lt, mk 20 [Tm.var 1, Tm.var 0]]
  mk 3 [mk 22 [tT, lt, g, nilT, Tm.var 1, Tm.var 0],
    mk 3 [mk 4 [mk 11 [tT, body1, Tm.var 1], mk 1 [r]],
      mk 3 [mk 11 [lt, mk 20 [Tm.var 2, Tm.var 0], r],
        mk 9 [mk 1 [Tm.var 1], mk 0 [leaf 0]]]]]

/-- The theorem: appending the empty list to a list gives the list, by induction on the list. -/
def induction : Tree := mk 23 [appendNil, Tm.var 0, mk 21 [tT, lt, g, nilT], step]

-- a theorem with a hypothesis: from `f = g`, `f x = g x`
#guard check (mk 4 [mk 0 [leaf 0], mk 1 [Tm.var 2]]) [] [arr, arr, tT]
    [⟨arr, Tm.var 0, Tm.var 1⟩] =
  some ⟨tT, mk 10 [Tm.var 0, Tm.var 2], mk 10 [Tm.var 1, Tm.var 2]⟩
-- a substitution: the first projection of a pair of a variable with itself is the variable, at
-- a quoted tree
#guard check (mk 20 [mk 15 [leaf 5], mk 13 [Tm.var 0, Tm.var 0]]) [] [] [] =
  some ⟨tT, mk 13 [mk 12 [mk 15 [leaf 5], mk 15 [leaf 5]]], mk 15 [leaf 5]⟩
-- an induction: appending the empty list to a list gives the list
#guard check induction [] [lt] [] = some ⟨lt, appendNil, Tm.var 0⟩
-- evaluation of a closed term
#guard check (mk 17 [apps (mk 22 [leaf 5]) [mk 15 [leaf 2], mk 15 [leaf 2]]]) [] [] [] =
  some ⟨tT, apps (mk 22 [leaf 5]) [mk 15 [leaf 2], mk 15 [leaf 2]], mk 15 [leaf 4]⟩
-- an altered binder: an abstraction whose annotation is not a type, and a β step whose
-- argument does not have the annotated type
#guard check (mk 5 [leaf 7, mk 1 [Tm.var 0]]) [] [] [] = none
#guard check (mk 11 [lt, Tm.var 0, mk 15 [leaf 1]]) [] [] [] = none
-- invalid dependencies: a hypothesis that is not there, and a transitivity whose middle terms
-- differ
#guard check (mk 0 [leaf 1]) [] [tT] [⟨tT, Tm.var 0, Tm.var 0⟩] = none
#guard check (mk 3 [mk 1 [Tm.var 0], mk 1 [mk 15 [leaf 0]]]) [] [tT] [] = none
-- false conclusions: evaluation does not conclude a wrong value, induction with a step that
-- does not prove its case fails, and the theorem does not conclude that the append is empty
#guard check (mk 17 [apps (mk 22 [leaf 5]) [mk 15 [leaf 2], mk 15 [leaf 2]]]) [] [] [] ≠
  some ⟨tT, apps (mk 22 [leaf 5]) [mk 15 [leaf 2], mk 15 [leaf 2]], mk 15 [leaf 5]⟩
#guard check (mk 23 [appendNil, Tm.var 0, mk 21 [tT, lt, g, nilT], mk 1 [Tm.var 0]]) [] [lt] [] =
  none
#guard check induction [] [lt] [] ≠ some ⟨lt, appendNil, nilT⟩

end Geb.Metalogic.Tests

end
