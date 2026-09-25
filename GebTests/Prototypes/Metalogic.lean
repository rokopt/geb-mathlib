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
public meta import Lean.Elab.Command -- shake: keep

set_option doc.verso true in
/-!
# The computational core's logic

Certificates checked by {name}`Geb.Metalogic.check`: a theorem with a hypothesis, derived by
congruence; a substitution, instantiating a variable of a derived equation; an induction on a
list, proving that appending the empty list to a list, written with the kernel's right fold,
gives the list; an induction on a label, proving that iterating the identity leaves its start
unchanged; an induction on a tree, proving that a fold whose step ignores its arguments is
constant; δ rules at literal trees and lists; the computation rules of the conditional and of
case analysis of lists; a reference to a definition of a loaded program; instances of the
axioms and of a theorem, each axiom's instance at the variables of its context being the axiom;
and iteration's reading of the label and the conditional as an iteration. Certificates with an
altered binder, an invalid dependency or a false conclusion do not check to that conclusion.

The checker written in Geb, {lit}`bootstrap/metalogic/equations.geb`, is compiled by the stage-0
compiler and compared with {name}`Geb.Metalogic.check` on these certificates, one of each rule
not among them, and malformed variants of each; agreement at each axiom's instance at its
variables makes the two checkers' tables of axioms agree. The malformed variants of a
certificate are its root relabelled with every rule's label and one beyond, and its root with
its last child removed. The source is read at elaboration by {lit}`include_str` and converted
to a list of characters inside the {lit}`#guard`, as in the stage-0 tests.

The numeral abbreviations of the prelude and of the Geb checker are compared with the Lean
abbreviations of the kernel's labels, the primitives' indices and the checker's rules, which
they must equal name for name and value for value; the comparison runs at elaboration and reads
the sources from the files.

## Main definitions

* {lit}`arr`, {lit}`lt` — the types of functions on trees and of lists of trees.
* {lit}`g`, {lit}`appendNil` — the step of appending and the append of the empty list.
* {lit}`step`, {lit}`induction` — the certificate of the inductive step and of the theorem.
* {lit}`idT`, {lit}`iterId`, {lit}`labelInduction` — iteration of the identity, and the
  certificate that it leaves its start unchanged, by induction on the label.
* {lit}`zeroStep`, {lit}`foldZero`, {lit}`treeInduction` — a fold whose step ignores its
  arguments, and the certificate that it is constant, by induction on the tree.
* {lit}`program`, {lit}`globals` — a program of one definition and the environment it loads.
* {lit}`chk` — the checker in a program's definitions, citing no theorems.
* {lit}`gebChecker`, {lit}`gebCheck?` — the Geb checker's program, and the checker compiled
  and loaded.
* {lit}`axiomId` — the certificate of an axiom's instance at the variables of its context.
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

/-- The checker in a program's definitions, citing no theorems. -/
def chk (c : Tree) (D : List Tree) : List Glob → Ctx → List Eqn → Option Eqn := check c ⟨D, []⟩

/-- The type of functions on trees. -/
def arr : Tree := tArrow tT tT

/-- The type of lists of trees. -/
def lt : Tree := tList tT

/-- The step of appending: a tree and a list to the list with the tree in front. -/
def g : Tree := mk Label.lam [tT, mk Label.lam [lt, mk Label.cons [Tm.var 1, Tm.var 0]]]

/-- The right fold of lists of trees at lists of trees. -/
def foldrL : Tree := mk Label.foldr [tT, lt]

/-- The empty list of trees. -/
def nilT : Tree := mk Label.nil [tT]

/-- The list of the innermost variable with the empty list appended. -/
def appendNil : Tree := apps foldrL [g, nilT, Tm.var 0]

/-- The inductive step, in the context of a tail and a head: the append of the head in front of
the tail is the head in front of the append of the tail, by the fold's computation and two β
steps, and that is the head in front of the tail by the hypothesis. -/
def step : Tree :=
  let r := appendNil
  let body1 := mk Label.lam [lt, mk Label.cons [Tm.var 1, Tm.var 0]]
  mk Rule.trans [mk Rule.foldrCons [tT, lt, g, nilT, Tm.var 1, Tm.var 0],
    mk Rule.trans [mk Rule.congApp [mk Rule.beta [tT, body1, Tm.var 1], mk Rule.refl [r]],
      mk Rule.trans [mk Rule.beta [lt, mk Label.cons [Tm.var 2, Tm.var 0], r],
        mk Rule.congCons [mk Rule.refl [Tm.var 1], mk Rule.hyp [leaf 0]]]]]

/-- The theorem: appending the empty list to a list gives the list, by induction on the list. -/
def induction : Tree := mk Rule.indList [appendNil, Tm.var 0, mk Rule.foldrNil [tT, lt, g, nilT],
    step]

-- a theorem with a hypothesis: from `f = g`, `f x = g x`
#guard chk (mk Rule.congApp [mk Rule.hyp [leaf 0], mk Rule.refl [Tm.var 2]]) [] [] [arr, arr, tT]
    [⟨arr, Tm.var 0, Tm.var 1⟩] =
  some ⟨tT, mk Label.app [Tm.var 0, Tm.var 2], mk Label.app [Tm.var 1, Tm.var 2]⟩
-- a substitution: the first projection of a pair of a variable with itself is the variable, at
-- a quoted tree
#guard chk (mk Rule.instVar [num 5, mk Rule.betaFst [Tm.var 0, Tm.var 0]]) [] [] [] [] =
  some ⟨tT, mk Label.fst [mk Label.pair [num 5, num 5]], num 5⟩
-- an induction: appending the empty list to a list gives the list
#guard chk induction [] [] [lt] [] = some ⟨lt, appendNil, Tm.var 0⟩
-- δ rules: a sum of labels, a node from a label and a list literal, and the list of a tree's
-- children
#guard chk (mk Rule.delta [leaf Prim.add, num 2, num 2]) [] [] [] [] =
  some ⟨tT, prim Prim.add [num 2, num 2], num 4⟩
#guard chk (mk Rule.delta [leaf Prim.node, num 7, listLit [leaf 1, leaf 2]]) [] [] [] [] =
  some ⟨tT, prim Prim.node [num 7, listLit [leaf 1, leaf 2]],
    mk Label.quote [mk 7 [leaf 1, leaf 2]]⟩
#guard chk (mk Rule.delta [leaf Prim.children,
    mk Label.quote [mk 7 [leaf 1, leaf 2]]]) [] [] [] [] =
  some ⟨lt, prim Prim.children [mk Label.quote [mk 7 [leaf 1, leaf 2]]], listLit [leaf 1, leaf 2]⟩
-- the conditional at a quoted tree whose label is not zero, and at one whose label is
#guard chk (mk Rule.condQuote [leaf 1, num 5, num 6]) [] [] [] [] =
  some ⟨tT, mk Label.cond [num 1, num 5, num 6], num 5⟩
#guard (chk (mk Rule.condQuote [leaf 0, Tm.var 0, num 6]) [] [] [tT] []).map (·.rhs) =
  some (num 6)
-- an altered binder: an abstraction whose annotation is not a type, and a β step whose
-- argument does not have the annotated type
#guard chk (mk Rule.congLam [leaf 7, mk Rule.refl [Tm.var 0]]) [] [] [] [] = none
#guard chk (mk Rule.beta [lt, Tm.var 0, num 1]) [] [] [] [] = none
-- invalid dependencies: a hypothesis that is not there, and a transitivity whose middle terms
-- differ
#guard chk (mk Rule.hyp [leaf 1]) [] [] [tT] [⟨tT, Tm.var 0, Tm.var 0⟩] = none
#guard chk (mk Rule.trans [mk Rule.refl [Tm.var 0], mk Rule.refl [num 0]]) [] [] [tT] [] = none
-- a δ rule at an argument that is not a literal, in a context that is not empty, and at a
-- partial application
#guard chk (mk Rule.delta [leaf Prim.add, prim Prim.add [num 1, num 1],
    num 2]) [] [] [] [] = none
#guard chk (mk Rule.delta [leaf Prim.add, num 2, num 2]) [] [] [tT] [] = none
#guard chk (mk Rule.delta [leaf Prim.add, num 2]) [] [] [] [] = none
-- false conclusions: a δ rule does not conclude a wrong value, induction with a step that
-- does not prove its case fails, and the theorem does not conclude that the append is empty
#guard chk (mk Rule.delta [leaf Prim.add, num 2, num 2]) [] [] [] [] ≠
  some ⟨tT, prim Prim.add [num 2, num 2], num 5⟩
#guard chk (mk Rule.indList [appendNil, Tm.var 0, mk Rule.foldrNil [tT, lt, g, nilT],
    mk Rule.refl [Tm.var 0]]) [] [] [lt] [] =
  none
#guard chk induction [] [] [lt] [] ≠ some ⟨lt, appendNil, nilT⟩

/-- The identity on trees. -/
def idT : Tree := mk Label.lam [tT, Tm.var 0]

/-- Iteration of the identity from the variable {lit}`1`, as many times as the label of the
variable {lit}`0`. -/
def iterId : Tree := apps (mk Label.iter [tT]) [idT, Tm.var 1, Tm.var 0]

/-- Iterating the identity leaves its start unchanged: at the label zero by iteration's
computation, and at a successor by iteration's computation, a β step and the hypothesis. -/
def labelInduction : Tree :=
  mk Rule.indLabel [iterId, Tm.var 1, mk Rule.iterZero [tT, idT, Tm.var 0],
    mk Rule.trans [mk Rule.iterSucc [tT, idT, Tm.var 1, Tm.var 0],
      mk Rule.trans [mk Rule.beta [tT, Tm.var 0, iterId], mk Rule.hyp [leaf 0]]]]

/-- The step of a fold that ignores its arguments. -/
def zeroStep : Tree := mk Label.lam [tT, mk Label.lam [lt, num 0]]

/-- The fold of the variable {lit}`0` by that step. -/
def foldZero : Tree := apps (mk Label.fold [tT]) [zeroStep, Tm.var 0]

/-- The fold by that step is constant: at a node by the fold's computation and two β steps. -/
def treeInduction : Tree :=
  let b := mapBy tT tT (apps (mk Label.fold [tT]) [zeroStep, Tm.var 1]) (Tm.var 0)
  mk Rule.indTree [foldZero, num 0,
    mk Rule.trans [mk Rule.foldNode [tT, zeroStep, Tm.var 1, Tm.var 0],
      mk Rule.trans [mk Rule.congApp [mk Rule.beta [tT, mk Label.lam [lt, num 0],
          mk Label.app [mk Label.prim [leaf Prim.label], Tm.var 1]],
          mk Rule.refl [b]],
        mk Rule.beta [lt, num 0, b]]]]

/-- A program of one definition, the tree of label five. -/
def program : List Tree := [num 5]

/-- The environment the program loads. -/
def globals : List Glob := (load program).getD []

-- an induction on a label: iterating the identity leaves its start unchanged
#guard chk labelInduction [] [] [tT, tT] [] =
  some ⟨tT,
      apps (mk Label.iter [tT]) [idT, Tm.var 1,
          mk Label.app [mk Label.prim [leaf Prim.label], Tm.var 0]], Tm.var 1⟩
-- an induction on a tree: a fold whose step ignores its arguments is constant
#guard chk treeInduction [] [] [tT] [] = some ⟨tT, foldZero, num 0⟩
-- case analysis of lists at the empty list and at a list of a head and a tail
#guard chk (mk Rule.lcaseNil [tT, tT, num 1,
    mk Label.lam [tT, mk Label.lam [lt, Tm.var 1]]]) [] [] [] [] =
  some ⟨tT,
      apps (mk Label.lcase [tT, tT]) [nilT, num 1, mk Label.lam [tT, mk Label.lam [lt, Tm.var 1]]],
    num 1⟩
#guard (chk (mk Rule.lcaseCons [tT, tT, num 2, nilT, num 1,
    mk Label.lam [tT, mk Label.lam [lt, Tm.var 1]]]) [] [] [] []).map (·.rhs) =
  some (apps (mk Label.lam [tT, mk Label.lam [lt, Tm.var 1]]) [num 2, nilT])
-- a reference to a definition, in the empty context and below a variable
#guard globals.length = 1
#guard chk (mk Rule.unfold [leaf 0]) program globals [] [] = some ⟨tT, mk Label.ref [leaf 0], num 5⟩
#guard chk (mk Rule.unfold [leaf 0]) program globals [tT] [] =
  some ⟨tT, mk Label.ref [leaf 0], num 5⟩
-- instances of axioms: the label of a node over the empty list in a context of one tree, and
-- the definition of addition at two numerals
#guard chk (mk Rule.ax [leaf 0, Tm.var 0, nilT]) [] [] [tT] [] =
  some ⟨tT, prim Prim.label [prim Prim.node [Tm.var 0, nilT]], prim Prim.label [Tm.var 0]⟩
#guard chk (mk Rule.ax [leaf 5, num 2, num 3]) [] [] [] [] =
  some ⟨tT, prim Prim.add [num 2, num 3],
    apps (mk Label.iter [tT]) [mk Label.lam [tT, succT (Tm.var 0)], prim Prim.label [num 2], num 3]⟩
-- an instance of a theorem, cited by its index among the theorems and not among the axioms
#guard check (mk Rule.thm [leaf 0, num 5])
    ⟨[], [⟨[tT], ⟨tT, prim Prim.label [Tm.var 0], Tm.var 0⟩⟩]⟩ [] [] [] =
  some ⟨tT, prim Prim.label [num 5], num 5⟩
#guard check (mk Rule.ax [leaf axioms.length, num 5])
    ⟨[], [⟨[tT], ⟨tT, prim Prim.label [Tm.var 0], Tm.var 0⟩⟩]⟩ [] [] [] = none
-- instances at a term of another type, at too few terms, and of an entry there is not
#guard chk (mk Rule.ax [leaf 0, num 1, num 2]) [] [] [] [] = none
#guard chk (mk Rule.ax [leaf 0, num 1]) [] [] [] [] = none
#guard chk (mk Rule.ax [leaf axioms.length, num 1]) [] [] [] [] = none
#guard chk (mk Rule.thm [leaf 0, num 1]) [] [] [] [] = none
-- iteration reads the label, and the conditional is an iteration
#guard chk (mk Rule.iterLabel [tT, idT, num 1, Tm.var 0]) [] [] [tT] [] =
  some ⟨tT, apps (mk Label.iter [tT]) [idT, num 1, Tm.var 0],
    apps (mk Label.iter [tT]) [idT, num 1,
        mk Label.app [mk Label.prim [leaf Prim.label], Tm.var 0]]⟩
#guard chk (mk Rule.condIter [tT, Tm.var 0, num 5, num 6]) [] [] [tT] [] =
  some ⟨tT, mk Label.cond [Tm.var 0, num 5, num 6],
      apps (mk Label.iter [tT]) [mk Label.lam [tT, num 5], num 6, Tm.var 0]⟩
#guard chk (mk Rule.condIter [tT, Tm.var 0, num 5, nilT]) [] [] [tT] [] = none
-- a reference to a definition the program does not have, an induction on a label in a context
-- whose innermost variable is not a tree, and a fold at a result type that is not a type
#guard chk (mk Rule.unfold [leaf 1]) program globals [] [] = none
#guard chk labelInduction [] [] [lt, tT] [] = none
#guard chk (mk Rule.foldNode [leaf 9, zeroStep, Tm.var 1, Tm.var 0]) [] [] [lt, tT] [] = none

/-- The metalogic's checker written in Geb. -/
def equationsGeb : String := include_str "../../bootstrap/metalogic/equations.geb"

/-- The program of the Geb checker: the prelude, the reader, the kernel's checker and the
metalogic's, applying the metalogic's checker to a node over a certificate, a program's
definitions, theorems about it, the types of its global environment, a context and a list of
hypotheses. -/
def gebChecker : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ equationsGeb ++ "\n" ++
    "(def main (lam ((x T)) (checkCert (children (child x 1)) (children (child x 2)) " ++
    "(children (child x 3)) (child x 0) (children (child x 4)) (children (child x 5)))))"

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

/-- A theorem as the Geb checker represents it: the node of label zero over the node of its
context and its equation. -/
def thmTree (th : Thm) : Tree := mk 0 [mk 0 th.ctx, eqnTree th.eqn]

/-- A checker's input: a certificate, a program's definitions and theorems about it, its global
environment, a context and a list of hypotheses. -/
abbrev Input : Type := Tree × Env × List Glob × Ctx × List Eqn

/-- Whether the Geb checker agrees with {name}`Geb.Metalogic.check` at an input, the Lean
checker's result represented as the Geb checker represents an optional equation. -/
def agrees (f : Tree → Option Tree) (x : Input) : Bool :=
  let (c, E, G, Γ, H) := x
  f (mk 0 [c, mk 0 E.defs, mk 0 (E.thms.map thmTree), mk 0 (G.map (·.1)), mk 0 Γ,
      mk 0 (H.map eqnTree)]) ==
    some ((check c E G Γ H).elim (leaf 0) fun q ↦ mk 1 [eqnTree q])

/-- The certificate instantiating the axiom of an index at the variables of its context. -/
def axiomId (j : ℕ) (th : Thm) : Tree :=
  mk Rule.ax (leaf j :: (List.range th.ctx.length).map Tm.var)

-- each axiom's instance at the variables of its context is the axiom
#guard ((List.range axioms.length).zip axioms).all fun (j, th) ↦
  chk (axiomId j th) [] [] th.ctx [] == some th.eqn

/-- The certificates of the rules the Lean checker is tested on above, and one of each rule not
tested there, with the definitions, environment, context and hypotheses they check in. -/
def programInputs : List (Tree × List Tree × List Glob × Ctx × List Eqn) :=
  [(mk Rule.congApp [mk Rule.hyp [leaf 0], mk Rule.refl [Tm.var 2]], [], [], [arr, arr, tT],
      [⟨arr, Tm.var 0, Tm.var 1⟩]),
   (mk Rule.instVar [num 5, mk Rule.betaFst [Tm.var 0, Tm.var 0]], [], [], [], []),
   (induction, [], [], [lt], []),
   (mk Rule.delta [leaf Prim.add, num 2, num 2], [], [], [], []),
   (mk Rule.delta [leaf Prim.node, num 7, listLit [leaf 1, leaf 2]], [], [], [], []),
   (mk Rule.delta [leaf Prim.children, mk Label.quote [mk 7 [leaf 1, leaf 2]]], [], [], [], []),
   (mk Rule.condQuote [leaf 1, num 5, num 6], [], [], [], []),
   (mk Rule.condQuote [leaf 0, Tm.var 0, num 6], [], [], [tT], []),
   (mk Rule.congLam [leaf 7, mk Rule.refl [Tm.var 0]], [], [], [], []),
   (mk Rule.beta [lt, Tm.var 0, num 1], [], [], [], []),
   (mk Rule.hyp [leaf 1], [], [], [tT], [⟨tT, Tm.var 0, Tm.var 0⟩]),
   (mk Rule.trans [mk Rule.refl [Tm.var 0], mk Rule.refl [num 0]], [], [], [tT], []),
   (mk Rule.delta [leaf Prim.add, prim Prim.add [num 1, num 1], num 2], [], [], [], []),
   (mk Rule.delta [leaf Prim.add, num 2, num 2], [], [], [tT], []),
   (mk Rule.delta [leaf Prim.add, num 2], [], [], [], []),
   (mk Rule.indList [appendNil, Tm.var 0, mk Rule.foldrNil [tT, lt, g, nilT],
       mk Rule.refl [Tm.var 0]], [], [], [lt], []),
   (labelInduction, [], [], [tT, tT], []),
   (treeInduction, [], [], [tT], []),
   (mk Rule.lcaseNil [tT, tT, num 1, mk Label.lam [tT, mk Label.lam [lt, Tm.var 1]]], [], [], [],
       []),
   (mk Rule.lcaseCons [tT, tT, num 2, nilT, num 1, mk Label.lam [tT, mk Label.lam [lt, Tm.var 1]]],
       [], [], [], []),
   (mk Rule.unfold [leaf 0], program, globals, [], []),
   (mk Rule.unfold [leaf 0], program, globals, [tT], []),
   (mk Rule.unfold [leaf 1], program, globals, [], []),
   (labelInduction, [], [], [lt, tT], []),
   (mk Rule.foldNode [leaf 9, zeroStep, Tm.var 1, Tm.var 0], [], [], [lt, tT], []),
   -- symmetry, congruence of abstraction, pairs, projections, lists and the conditional
   (mk Rule.symm [mk Rule.refl [num 5]], [], [], [], []),
   (mk Rule.congLam [tT, mk Rule.refl [Tm.var 0]], [], [], [], []),
   (mk Rule.congPair [mk Rule.refl [num 1], mk Rule.refl [num 2]], [], [], [], []),
   (mk Rule.congFst [mk Rule.refl [mk Label.pair [num 1, num 2]]], [], [], [], []),
   (mk Rule.congSnd [mk Rule.refl [mk Label.pair [num 1, num 2]]], [], [], [], []),
   (mk Rule.congCons [mk Rule.refl [num 1], mk Rule.refl [nilT]], [], [], [], []),
   (mk Rule.congCond [mk Rule.refl [num 1], mk Rule.refl [num 2], mk Rule.refl [num 3]], [], [],
       [], []),
   -- the η rules, the β rules of pairs, weakening, cut, the right fold and iteration
   (mk Rule.eta [Tm.var 0], [], [], [arr], []),
   (mk Rule.betaFst [num 1, mk Label.unit []], [], [], [], []),
   (mk Rule.betaSnd [num 1, num 2], [], [], [], []),
   (mk Rule.etaPair [Tm.var 0], [], [], [tProd tT tT], []),
   (mk Rule.etaUnit [Tm.var 0], [], [], [tUnit], []),
   (mk Rule.weaken [mk Rule.refl [num 1]], [], [], [tT], [⟨tT, Tm.var 0, num 1⟩]),
   (mk Rule.cut [mk Rule.refl [num 1], mk Rule.hyp [leaf 0]], [], [], [], []),
   (mk Rule.foldrNil [tT, lt, g, nilT], [], [], [], []),
   (mk Rule.foldrCons [tT, lt, g, nilT, num 1, nilT], [], [], [], []),
   (mk Rule.iterZero [tT, idT, num 1], [], [], [], []),
   (mk Rule.iterSucc [tT, idT, num 1, num 3], [], [], [], []),
   (mk Rule.foldNode [tT, zeroStep, num 1, nilT], [], [], [], []),
   -- the δ rules of every primitive
   (mk Rule.delta [leaf Prim.label, mk Label.quote [mk 3 [leaf 1]]], [], [], [], []),
   (mk Rule.delta [leaf Prim.arity, mk Label.quote [mk 3 [leaf 1]]], [], [], [], []),
   (mk Rule.delta [leaf Prim.child, mk Label.quote [mk 3 [leaf 1, leaf 9]], num 1], [], [], [], []),
   (mk Rule.delta [leaf Prim.sub, num 7, num 9], [], [], [], []),
   (mk Rule.delta [leaf Prim.mul, num 7, num 9], [], [], [], []),
   (mk Rule.delta [leaf Prim.div, num 9, num 2], [], [], [], []),
   (mk Rule.delta [leaf Prim.mod, num 9, num 2], [], [], [], []),
   (mk Rule.delta [leaf Prim.eq, num 9, num 9], [], [], [], []),
   (mk Rule.delta [leaf Prim.lt, num 2, num 9], [], [], [], []),
   (mk Rule.delta [leaf Prim.equal, mk Label.quote [mk 3 [leaf 1]],
       mk Label.quote [mk 3 [leaf 1]]], [], [], [], []),
   (mk Rule.delta [leaf Prim.log2, num 9], [], [], [], []),
   (mk Rule.delta [leaf 14, num 9], [], [], [], [])]

/-- The inputs compared: each axiom's instance at the variables of its context, the instances
and rules tested above, and the certificates of {lit}`programInputs`, citing no theorems. -/
def inputs : List Input :=
  ((List.range axioms.length).zip axioms).map
      (fun (j, th) ↦ (axiomId j th, ⟨[], []⟩, [], th.ctx, [])) ++
  [(mk Rule.thm [leaf 0, num 5], ⟨[], [⟨[tT], ⟨tT, prim Prim.label [Tm.var 0], Tm.var 0⟩⟩]⟩, [], [],
      []),
   (mk Rule.ax [leaf axioms.length, num 5],
      ⟨[], [⟨[tT], ⟨tT, prim Prim.label [Tm.var 0], Tm.var 0⟩⟩]⟩, [], [], []),
   (mk Rule.ax [leaf 0, Tm.var 0, nilT], ⟨[], []⟩, [], [tT], []),
   (mk Rule.ax [leaf 5, num 2, num 3], ⟨[], []⟩, [], [], []),
   (mk Rule.ax [leaf 0, num 1, num 2], ⟨[], []⟩, [], [], []),
   (mk Rule.ax [leaf axioms.length, num 1], ⟨[], []⟩, [], [], []),
   (mk Rule.thm [leaf 0, num 1], ⟨[], []⟩, [], [], []),
   (mk Rule.iterLabel [tT, idT, num 1, Tm.var 0], ⟨[], []⟩, [], [tT], []),
   (mk Rule.condIter [tT, Tm.var 0, num 5, num 6], ⟨[], []⟩, [], [tT], []),
   (mk Rule.condIter [tT, Tm.var 0, num 5, nilT], ⟨[], []⟩, [], [tT], [])] ++
  programInputs.map fun (c, D, G, Γ, H) ↦ (c, ⟨D, []⟩, G, Γ, H)

/-- Malformed variants of an input: its certificate's root relabelled with every rule's label
and one beyond, and with its last child removed. -/
def mutants (x : Input) : List Input :=
  let (c, rest) := x
  ((List.range 38).map fun l ↦ (mk l c.children, rest)) ++ [(mk c.label c.children.dropLast, rest)]

-- the Geb checker agrees with the Lean checker on every input and on its malformed variants,
-- which include the input
#guard (gebCheck? Kernel.Stage0Tests.compiler.toList gebChecker.toList).any fun f ↦
  (inputs.flatMap mutants).all (agrees f)

-- the numeral abbreviations of the prelude and the Geb checker are the Lean abbreviations of
-- the kernel's labels, the primitives' indices and the checker's rules, name for name and value
-- for value
open Lean Elab Command Meta in
run_cmd do
  let defnums (text : String) : List (String × ℕ) :=
    ((readSExps text.toList).getD []).filterMap fun e ↦
      match e.children with
      | [kw, n, v] =>
        if kw.label.map String.ofList == some "defnum" then
          do some (String.ofList (← n.label), ← numeral? (← v.label))
        else none
      | _ => none
  let mut geb := []
  for f in ["bootstrap/prelude.geb", "bootstrap/metalogic/equations.geb"] do
    geb := geb ++ defnums (← IO.FS.readFile f)
  let spaces := [`Geb.Kernel.Label, `Geb.Kernel.Prim, `Geb.Metalogic.Rule]
  let consts := (← getEnv).constants.fold (init := #[]) fun acc c info ↦
    if spaces.contains c.getPrefix then acc.push (c, info) else acc
  let lean ← liftTermElabM <| consts.toList.filterMapM fun (c, info) ↦ do
    let some v := info.value? | return none
    return (← (evalNat v).run).map ((c.replacePrefix c.getPrefix.getPrefix .anonymous).toString, ·)
  unless geb.length == lean.length && geb.all lean.contains do
    throwError "the Geb abbreviations {geb} are not the Lean abbreviations {lean}"

end Geb.Metalogic.Tests


end
