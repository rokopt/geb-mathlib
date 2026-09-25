/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Metalogic -- shake: keep
public meta import Geb.Prototypes.Metalogic -- shake: keep
public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep

set_option doc.verso true in
/-!
# The first rung of the metalogic

Certificates checked by {name}`Geb.Metalogic.check`: a theorem with a hypothesis, derived by
congruence; a substitution, instantiating a variable of a derived equation; an induction on a
list, proving that appending the empty list to a list, written with the kernel's right fold,
gives the list; an induction on a label, proving that iterating the identity leaves its start
unchanged; an induction on a tree, proving that a fold whose step ignores its arguments is
constant; δ rules at literal trees and lists; the computation rules of the conditional and of
case analysis of lists; and a reference to a definition of a loaded program. Certificates with
an altered binder, an invalid dependency or a false conclusion do not check to that
conclusion.

The checker written in Geb, {lit}`bootstrap/metalogic/equations.geb`, is compiled by the stage-0
compiler and compared with {name}`Geb.Metalogic.check` on these certificates, one of each rule
not among them, and malformed variants of each: its root relabelled with every rule's label and
one beyond, and its last child removed. The source is read at elaboration by
{lit}`include_str` and converted to a list of characters inside the {lit}`#guard`, as in the
stage-0 tests.

## Main definitions

* {lit}`arr`, {lit}`lt` — the types of functions on trees and of lists of trees.
* {lit}`g`, {lit}`appendNil` — the step of appending and the append of the empty list.
* {lit}`step`, {lit}`induction` — the certificate of the inductive step and of the theorem.
* {lit}`idT`, {lit}`iterId`, {lit}`labelInduction` — iteration of the identity, and the
  certificate that it leaves its start unchanged, by induction on the label.
* {lit}`zeroStep`, {lit}`foldZero`, {lit}`treeInduction` — a fold whose step ignores its
  arguments, and the certificate that it is constant, by induction on the tree.
* {lit}`program`, {lit}`globals` — a program of one definition and the environment it loads.
* {lit}`gebChecker`, {lit}`gebCheck?` — the Geb checker's program, and the checker compiled
  and loaded.
* {lit}`inputs`, {lit}`mutants`, {lit}`agrees` — the inputs compared, their malformed variants,
  and the agreement of the two checkers at an input.

## Tags

bootstrap, metalogic, proof certificate, differential testing, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Metalogic.Tests

open Geb.Kernel
open scoped FinEnum

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
#guard check (mk 4 [mk 0 [leaf 0], mk 1 [Tm.var 2]]) [] [] [arr, arr, tT]
    [⟨arr, Tm.var 0, Tm.var 1⟩] =
  some ⟨tT, mk 10 [Tm.var 0, Tm.var 2], mk 10 [Tm.var 1, Tm.var 2]⟩
-- a substitution: the first projection of a pair of a variable with itself is the variable, at
-- a quoted tree
#guard check (mk 20 [mk 15 [leaf 5], mk 13 [Tm.var 0, Tm.var 0]]) [] [] [] [] =
  some ⟨tT, mk 13 [mk 12 [mk 15 [leaf 5], mk 15 [leaf 5]]], mk 15 [leaf 5]⟩
-- an induction: appending the empty list to a list gives the list
#guard check induction [] [] [lt] [] = some ⟨lt, appendNil, Tm.var 0⟩
-- δ rules: a sum of labels, a node from a label and a list literal, and the list of a tree's
-- children
#guard check (mk 17 [leaf 5, mk 15 [leaf 2], mk 15 [leaf 2]]) [] [] [] [] =
  some ⟨tT, apps (mk 22 [leaf 5]) [mk 15 [leaf 2], mk 15 [leaf 2]], mk 15 [leaf 4]⟩
#guard check (mk 17 [leaf 3, mk 15 [leaf 7], listLit [leaf 1, leaf 2]]) [] [] [] [] =
  some ⟨tT, apps (mk 22 [leaf 3]) [mk 15 [leaf 7], listLit [leaf 1, leaf 2]],
    mk 15 [mk 7 [leaf 1, leaf 2]]⟩
#guard check (mk 17 [leaf 4, mk 15 [mk 7 [leaf 1, leaf 2]]]) [] [] [] [] =
  some ⟨lt, apps (mk 22 [leaf 4]) [mk 15 [mk 7 [leaf 1, leaf 2]]], listLit [leaf 1, leaf 2]⟩
-- the conditional at a quoted tree whose label is not zero, and at one whose label is
#guard check (mk 32 [leaf 1, mk 15 [leaf 5], mk 15 [leaf 6]]) [] [] [] [] =
  some ⟨tT, mk 16 [mk 15 [leaf 1], mk 15 [leaf 5], mk 15 [leaf 6]], mk 15 [leaf 5]⟩
#guard (check (mk 32 [leaf 0, Tm.var 0, mk 15 [leaf 6]]) [] [] [tT] []).map (·.rhs) =
  some (mk 15 [leaf 6])
-- an altered binder: an abstraction whose annotation is not a type, and a β step whose
-- argument does not have the annotated type
#guard check (mk 5 [leaf 7, mk 1 [Tm.var 0]]) [] [] [] [] = none
#guard check (mk 11 [lt, Tm.var 0, mk 15 [leaf 1]]) [] [] [] [] = none
-- invalid dependencies: a hypothesis that is not there, and a transitivity whose middle terms
-- differ
#guard check (mk 0 [leaf 1]) [] [] [tT] [⟨tT, Tm.var 0, Tm.var 0⟩] = none
#guard check (mk 3 [mk 1 [Tm.var 0], mk 1 [mk 15 [leaf 0]]]) [] [] [tT] [] = none
-- a δ rule at an argument that is not a literal, in a context that is not empty, and at a
-- partial application
#guard check (mk 17 [leaf 5, apps (mk 22 [leaf 5]) [mk 15 [leaf 1], mk 15 [leaf 1]],
    mk 15 [leaf 2]]) [] [] [] [] = none
#guard check (mk 17 [leaf 5, mk 15 [leaf 2], mk 15 [leaf 2]]) [] [] [tT] [] = none
#guard check (mk 17 [leaf 5, mk 15 [leaf 2]]) [] [] [] [] = none
-- false conclusions: a δ rule does not conclude a wrong value, induction with a step that
-- does not prove its case fails, and the theorem does not conclude that the append is empty
#guard check (mk 17 [leaf 5, mk 15 [leaf 2], mk 15 [leaf 2]]) [] [] [] [] ≠
  some ⟨tT, apps (mk 22 [leaf 5]) [mk 15 [leaf 2], mk 15 [leaf 2]], mk 15 [leaf 5]⟩
#guard check (mk 23 [appendNil, Tm.var 0, mk 21 [tT, lt, g, nilT], mk 1 [Tm.var 0]]) [] [] [lt] [] =
  none
#guard check induction [] [] [lt] [] ≠ some ⟨lt, appendNil, nilT⟩

/-- The identity on trees. -/
def idT : Tree := mk 9 [tT, Tm.var 0]

/-- Iteration of the identity from the variable {lit}`1`, as many times as the label of the
variable {lit}`0`. -/
def iterId : Tree := apps (mk 18 [tT]) [idT, Tm.var 1, Tm.var 0]

/-- Iterating the identity leaves its start unchanged: at the label zero by iteration's
computation, and at a successor by iteration's computation, a β step and the hypothesis. -/
def labelInduction : Tree :=
  mk 30 [iterId, Tm.var 1, mk 26 [tT, idT, Tm.var 0],
    mk 3 [mk 27 [tT, idT, Tm.var 1, Tm.var 0],
      mk 3 [mk 11 [tT, Tm.var 0, iterId], mk 0 [leaf 0]]]]

/-- The step of a fold that ignores its arguments. -/
def zeroStep : Tree := mk 9 [tT, mk 9 [lt, mk 15 [leaf 0]]]

/-- The fold of the variable {lit}`0` by that step. -/
def foldZero : Tree := apps (mk 17 [tT]) [zeroStep, Tm.var 0]

/-- The fold by that step is constant: at a node by the fold's computation and two β steps. -/
def treeInduction : Tree :=
  let b := mapBy tT tT (apps (mk 17 [tT]) [zeroStep, Tm.var 1]) (Tm.var 0)
  mk 29 [foldZero, mk 15 [leaf 0],
    mk 3 [mk 28 [tT, zeroStep, Tm.var 1, Tm.var 0],
      mk 3 [mk 4 [mk 11 [tT, mk 9 [lt, mk 15 [leaf 0]], mk 10 [mk 22 [leaf 0], Tm.var 1]],
          mk 1 [b]],
        mk 11 [lt, mk 15 [leaf 0], b]]]]

/-- A program of one definition, the tree of label five. -/
def program : List Tree := [mk 15 [leaf 5]]

/-- The environment the program loads. -/
def globals : List Glob := (load program).getD []

-- an induction on a label: iterating the identity leaves its start unchanged
#guard check labelInduction [] [] [tT, tT] [] =
  some ⟨tT, apps (mk 18 [tT]) [idT, Tm.var 1, mk 10 [mk 22 [leaf 0], Tm.var 0]], Tm.var 1⟩
-- an induction on a tree: a fold whose step ignores its arguments is constant
#guard check treeInduction [] [] [tT] [] = some ⟨tT, foldZero, mk 15 [leaf 0]⟩
-- case analysis of lists at the empty list and at a list of a head and a tail
#guard check (mk 24 [tT, tT, mk 15 [leaf 1], mk 9 [tT, mk 9 [lt, Tm.var 1]]]) [] [] [] [] =
  some ⟨tT, apps (mk 24 [tT, tT]) [nilT, mk 15 [leaf 1], mk 9 [tT, mk 9 [lt, Tm.var 1]]],
    mk 15 [leaf 1]⟩
#guard (check (mk 25 [tT, tT, mk 15 [leaf 2], nilT, mk 15 [leaf 1],
    mk 9 [tT, mk 9 [lt, Tm.var 1]]]) [] [] [] []).map (·.rhs) =
  some (apps (mk 9 [tT, mk 9 [lt, Tm.var 1]]) [mk 15 [leaf 2], nilT])
-- a reference to a definition, in the empty context and below a variable
#guard globals.length = 1
#guard check (mk 31 [leaf 0]) program globals [] [] = some ⟨tT, mk 23 [leaf 0], mk 15 [leaf 5]⟩
#guard check (mk 31 [leaf 0]) program globals [tT] [] =
  some ⟨tT, mk 23 [leaf 0], mk 15 [leaf 5]⟩
-- a reference to a definition the program does not have, an induction on a label in a context
-- whose innermost variable is not a tree, and a fold at a result type that is not a type
#guard check (mk 31 [leaf 1]) program globals [] [] = none
#guard check labelInduction [] [] [lt, tT] [] = none
#guard check (mk 28 [leaf 9, zeroStep, Tm.var 1, Tm.var 0]) [] [] [lt, tT] [] = none

/-- The metalogic's checker written in Geb. -/
def equationsGeb : String := include_str "../../bootstrap/metalogic/equations.geb"

/-- The program of the Geb checker: the prelude, the reader, the kernel's checker and the
metalogic's, applying the metalogic's checker to a node over a certificate, a program's
definitions, the types of its global environment, a context and a list of hypotheses. -/
def gebChecker : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ equationsGeb ++ "\n" ++
    "(def main (lam ((x T)) (checkCert (children (child x 1)) (children (child x 2)) " ++
    "(child x 0) (children (child x 3)) (children (child x 4)))))"

/-- The Geb checker, compiled by the stage-0 compiler and loaded, as a function on trees, given
the texts of the compiler and the checker's program. -/
def gebCheck? (compilerText checkerText : List Char) : Option (Tree → Option Tree) := do
  let img ← runMain compilerText (nameTree checkerText)
  let ds ← unbundle (← readImage (← toBytes img))
  let G ← load (ds.map Prod.snd)
  let main ← G.getLast?
  some main.apply

/-- An equation as the Geb checker represents it: the node of label zero over its type and its
sides. -/
def eqnTree (q : Eqn) : Tree := mk 0 [q.ty, q.lhs, q.rhs]

/-- A checker's input: a certificate, a program's definitions, its global environment, a context
and a list of hypotheses. -/
abbrev Input : Type := Tree × List Tree × List Glob × Ctx × List Eqn

/-- Whether the Geb checker agrees with {name}`Geb.Metalogic.check` at an input, the Lean
checker's result represented as the Geb checker represents an optional equation. -/
def agrees (f : Tree → Option Tree) (x : Input) : Bool :=
  let (c, D, G, Γ, H) := x
  f (mk 0 [c, mk 0 D, mk 0 (G.map (·.1)), mk 0 Γ, mk 0 (H.map eqnTree)]) ==
    some ((check c D G Γ H).elim (leaf 0) fun q ↦ mk 1 [eqnTree q])

/-- The certificates the Lean checker is tested on above, and one of each rule not tested there,
with the inputs they check in. -/
def inputs : List Input :=
  let q := fun n ↦ mk 15 [leaf n]
  [(mk 4 [mk 0 [leaf 0], mk 1 [Tm.var 2]], [], [], [arr, arr, tT], [⟨arr, Tm.var 0, Tm.var 1⟩]),
   (mk 20 [q 5, mk 13 [Tm.var 0, Tm.var 0]], [], [], [], []),
   (induction, [], [], [lt], []),
   (mk 17 [leaf 5, q 2, q 2], [], [], [], []),
   (mk 17 [leaf 3, q 7, listLit [leaf 1, leaf 2]], [], [], [], []),
   (mk 17 [leaf 4, mk 15 [mk 7 [leaf 1, leaf 2]]], [], [], [], []),
   (mk 32 [leaf 1, q 5, q 6], [], [], [], []),
   (mk 32 [leaf 0, Tm.var 0, q 6], [], [], [tT], []),
   (mk 5 [leaf 7, mk 1 [Tm.var 0]], [], [], [], []),
   (mk 11 [lt, Tm.var 0, q 1], [], [], [], []),
   (mk 0 [leaf 1], [], [], [tT], [⟨tT, Tm.var 0, Tm.var 0⟩]),
   (mk 3 [mk 1 [Tm.var 0], mk 1 [q 0]], [], [], [tT], []),
   (mk 17 [leaf 5, apps (mk 22 [leaf 5]) [q 1, q 1], q 2], [], [], [], []),
   (mk 17 [leaf 5, q 2, q 2], [], [], [tT], []),
   (mk 17 [leaf 5, q 2], [], [], [], []),
   (mk 23 [appendNil, Tm.var 0, mk 21 [tT, lt, g, nilT], mk 1 [Tm.var 0]], [], [], [lt], []),
   (labelInduction, [], [], [tT, tT], []),
   (treeInduction, [], [], [tT], []),
   (mk 24 [tT, tT, q 1, mk 9 [tT, mk 9 [lt, Tm.var 1]]], [], [], [], []),
   (mk 25 [tT, tT, q 2, nilT, q 1, mk 9 [tT, mk 9 [lt, Tm.var 1]]], [], [], [], []),
   (mk 31 [leaf 0], program, globals, [], []),
   (mk 31 [leaf 0], program, globals, [tT], []),
   (mk 31 [leaf 1], program, globals, [], []),
   (labelInduction, [], [], [lt, tT], []),
   (mk 28 [leaf 9, zeroStep, Tm.var 1, Tm.var 0], [], [], [lt, tT], []),
   -- symmetry, congruence of abstraction, pairs, projections, lists and the conditional
   (mk 2 [mk 1 [q 5]], [], [], [], []),
   (mk 5 [tT, mk 1 [Tm.var 0]], [], [], [], []),
   (mk 6 [mk 1 [q 1], mk 1 [q 2]], [], [], [], []),
   (mk 7 [mk 1 [mk 12 [q 1, q 2]]], [], [], [], []),
   (mk 8 [mk 1 [mk 12 [q 1, q 2]]], [], [], [], []),
   (mk 9 [mk 1 [q 1], mk 1 [nilT]], [], [], [], []),
   (mk 10 [mk 1 [q 1], mk 1 [q 2], mk 1 [q 3]], [], [], [], []),
   -- the η rules, the β rules of pairs, weakening, cut, the right fold and iteration
   (mk 12 [Tm.var 0], [], [], [arr], []),
   (mk 13 [q 1, mk 11 []], [], [], [], []),
   (mk 14 [q 1, q 2], [], [], [], []),
   (mk 15 [Tm.var 0], [], [], [tProd tT tT], []),
   (mk 16 [Tm.var 0], [], [], [tUnit], []),
   (mk 18 [mk 1 [q 1]], [], [], [tT], [⟨tT, Tm.var 0, q 1⟩]),
   (mk 19 [mk 1 [q 1], mk 0 [leaf 0]], [], [], [], []),
   (mk 21 [tT, lt, g, nilT], [], [], [], []),
   (mk 22 [tT, lt, g, nilT, q 1, nilT], [], [], [], []),
   (mk 26 [tT, idT, q 1], [], [], [], []),
   (mk 27 [tT, idT, q 1, q 3], [], [], [], []),
   (mk 28 [tT, zeroStep, q 1, nilT], [], [], [], []),
   -- the δ rules of every primitive
   (mk 17 [leaf 0, mk 15 [mk 3 [leaf 1]]], [], [], [], []),
   (mk 17 [leaf 1, mk 15 [mk 3 [leaf 1]]], [], [], [], []),
   (mk 17 [leaf 2, mk 15 [mk 3 [leaf 1, leaf 9]], q 1], [], [], [], []),
   (mk 17 [leaf 6, q 7, q 9], [], [], [], []),
   (mk 17 [leaf 7, q 7, q 9], [], [], [], []),
   (mk 17 [leaf 8, q 9, q 2], [], [], [], []),
   (mk 17 [leaf 9, q 9, q 2], [], [], [], []),
   (mk 17 [leaf 10, q 9, q 9], [], [], [], []),
   (mk 17 [leaf 11, q 2, q 9], [], [], [], []),
   (mk 17 [leaf 12, mk 15 [mk 3 [leaf 1]], mk 15 [mk 3 [leaf 1]]], [], [], [], []),
   (mk 17 [leaf 13, q 9], [], [], [], []),
   (mk 17 [leaf 14, q 9], [], [], [], [])]

/-- Malformed variants of an input: its certificate's root relabelled with every rule's label
and one beyond, and with its last child removed. -/
def mutants (x : Input) : List Input :=
  let (c, rest) := x
  ((List.range 34).map fun l ↦ (mk l c.children, rest)) ++ [(mk c.label c.children.dropLast, rest)]

-- the Geb checker agrees with the Lean checker on every input and on its malformed variants,
-- which include the input
#guard (gebCheck? Kernel.Stage0Tests.compiler.toList gebChecker.toList).any fun f ↦
  (inputs.flatMap mutants).all (agrees f)

end Geb.Metalogic.Tests


end
