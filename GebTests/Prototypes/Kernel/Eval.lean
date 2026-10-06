/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Eval -- shake: keep
public meta import Geb.Prototypes.Kernel.Eval -- shake: keep
public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep

set_option doc.verso true in
/-!
# Evaluator examples

The evaluator of kernel terms ({name}`Geb.Kernel.Eval.eval`) computes the application of an
abstraction, a fold of trees, the primitives on trees and lists, a conditional, a reference to a
definition, iteration, the right fold and case analysis of lists, and a partial application, and
fails at fuel that does not suffice. The evaluator written in Geb, {lit}`bootstrap/eval.geb`,
loaded after the prelude, agrees with Lean's on each example at each level of fuel up to one that
suffices.

## Tags

evaluator, kernel, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.EvalTests

open Geb.Kernel.Eval Geb.Kernel.Stage0Tests
open scoped FinEnum

/-- A node. -/
def nd (l : ℕ) (cs : List Tree) : Tree := RoseTree.node l cs

/-- A variable. -/
def var (i : ℕ) : Tree := nd Label.var [leaf i]

/-- A quoted tree. -/
def q (t : Tree) : Tree := nd Label.quote [t]

/-- An abstraction. -/
def lam (A b : Tree) : Tree := nd Label.lam [A, b]

/-- An application. -/
def app (f x : Tree) : Tree := nd Label.app [f, x]

/-- A primitive. -/
def prim (k : ℕ) : Tree := nd Label.prim [leaf k]

/-- The size of a tree, by the fold of trees and the right fold of lists. -/
def size : Tree :=
  app (nd Label.fold [tT]) (lam tT (lam (tList tT)
    (app (app (app (nd Label.foldr [tT, tT]) (prim Prim.add)) (q (leaf 1))) (var 0))))

/-- A tree of five nodes. -/
def five : Tree := nd 3 [leaf 0, nd 4 [leaf 1, leaf 2]]

/-- Examples: a program's definitions, and a term with its expected value. -/
def examples : List (List Tree × Tree × Tree) :=
  [([], app (lam tT (var 0)) (q (leaf 7)), Val.quote (leaf 7)),
   ([], app size (q five), Val.quote (leaf 5)),
   ([], app (app (prim Prim.node) (q (leaf 9))) (app (prim Prim.children) (q five)),
     Val.quote (nd 9 [leaf 0, nd 4 [leaf 1, leaf 2]])),
   ([], nd Label.cond [q (leaf 0), q (leaf 1), q (leaf 2)], Val.quote (leaf 2)),
   ([lam tT (app (app (prim Prim.add) (var 0)) (var 0))], app (nd Label.ref [leaf 0]) (q (leaf 4)),
     Val.quote (leaf 8)),
   ([], app (app (app (nd Label.iter [tT]) (app (prim Prim.add) (q (leaf 3)))) (q (leaf 1)))
     (q (leaf 4)), Val.quote (leaf 13)),
   ([], app (app (app (nd Label.lcase [tT, tT]) (app (prim Prim.children) (q five))) (q (leaf 0)))
     (lam tT (lam (tList tT) (var 1))), Val.quote (leaf 0)),
   ([], app (nd Label.fold [tT]) (q (leaf 0)),
     Val.app (nd Label.fold [tT]) (Val.quote (leaf 0)))]

-- each example evaluates to its value at enough fuel, and fails at none
#guard examples.all fun (G, t, v) ↦ eval G 20 [] t == some v && eval G 0 [] t == none

/-- The source of the evaluator written in Geb. -/
def evalGeb : String := include_str "../../../bootstrap/eval.geb"

/-- A program's definitions, read by the front end whose text is {lit}`fe` and loaded: each
definition's name with its global. -/
def loadedEval (fe text : List Char) : Option (List (List Char × Glob)) := do
  let r ← runMain fe (nameTree text)
  let b ← if r.label == 1 then r.children.head? else none
  let ds ← unbundle b
  let G ← load (ds.map Prod.snd)
  some ((ds.map Prod.fst).zip G)

/-- The evaluator written in Geb, among a loaded program's definitions, at its type: from the
definitions, the fuel, the environment and the term to the optional value. -/
def gebEval (P : List (List Char × Glob)) :
    Option (List Tree → Tree → List Tree → Tree → Tree) := do
  let (_, g) ← P.find? (·.1 == ['E', 'v', 'a', 'l', '.', 'e', 'v', 'a', 'l'])
  let A := tArrow (tList tT) (tArrow tT (tArrow (tList tT) (tArrow tT tT)))
  if h : g.1 = A then some (cast (congrArg Ty.den h) g.2) else none

/-- An optional value as the prelude's optional tree. -/
def encOpt : Option Tree → Tree
  | some v => RoseTree.node 1 [v]
  | none => leaf 0

-- the evaluator written in Geb agrees with Lean's on each example at each level of fuel
#guard ((loadedEval bundler.toList (prelude ++ "\n" ++ evalGeb ++ "\n").toList).bind gebEval).any
    fun f ↦ examples.all fun (G, t, _) ↦
  (List.range 21).all fun n ↦ f G (leaf n) [] t == encOpt (eval G n [] t)

end Geb.Kernel.EvalTests

end
