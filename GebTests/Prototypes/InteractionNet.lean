/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Data -- shake: keep
public import Geb.Prototypes.InteractionNet.Kernel
public import GebTests.Prototypes.InteractionNet.Wiring -- shake: keep
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
public import GebTests.Prototypes.Kernel -- shake: keep
public meta import Geb.Prototypes.InteractionNet.Data -- shake: keep
public meta import Geb.Prototypes.InteractionNet.Kernel -- shake: keep
public meta import GebTests.Prototypes.Kernel -- shake: keep

set_option doc.verso true in
/-!
# Interaction-net execution tests

Constructor copying and erasure exercise explicit allocation and wire elimination. Kernel
programs exercise closures, globals, arithmetic, conditional thunks and the recursors, using
the same program texts as the kernel's denotational tests.

## Main definitions

* {lit}`runText` — read a program and execute its final definition on the net machine.

## Tags

interaction net, kernel, regression test, copying, read-back
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Tests

open Geb.Kernel
open scoped FinEnum

#guard Data.readInterface (Data.system.run 30 (Data.copyInput 2
    (RoseTree.node 7 [leaf 3, RoseTree.node 9 [leaf 11]]))) =
  some (List.replicate 2 (RoseTree.node 7 [leaf 3, RoseTree.node 9 [leaf 11]]))
#guard (Data.system.run 10
  (Data.copyInput 0 (RoseTree.node 7 [leaf 3, leaf 5]))).equations.isEmpty
#guard Data.readInterface (Data.system.run 20 (Data.copyInput 3 (leaf (2 ^ 100)))) =
  some (List.replicate 3 (leaf (2 ^ 100)))

-- Either orientation of a variable equation can supply the connected interface.
#guard ((Data.system.step
  { interface := [Term.var 1], equations := [(Term.var 0, Term.var 1)], nextName := 2 }).map
    (fun c ↦ c.equations.isEmpty && c.names == [0])) = some true

-- An inert pair at the front does not prevent a later erasure from reducing.
#guard ((Data.system.step
  { interface := []
    equations := [(Data.encode (leaf 1), Data.encode (leaf 2)),
      (Term.agent (Data.fan 0) Fin.elim0, Data.encode (leaf 3))]
    nextName := 0 }).map (fun c ↦ c.equations.length)) = some 1

-- The occurs check preserves a cyclic wire instead of substituting it into itself.
#guard (Data.system.step
  { interface := []
    equations := [(Term.var 0, Term.agent (Data.node 7 1) (fun _ ↦ Term.var 0))]
    nextName := 1 }).isNone

/-- Execute the last definition of a parsed program on the interaction machine. -/
def runText (steps : ℕ) (text : List Char) (input : Tree) : Option Tree := do
  let ds ← readProgram text
  let P := ds.map Prod.snd
  let G ← load P
  if (← G.getLast?).1 = tArrow tT tT then
    Kernel.run P steps (← P.getLast?) input
  else none

#guard runText 1000 "(def id (lam (x T) x))".toList (leaf 7) = some (leaf 7)
#guard runText 1000 "(def add1 (lam (x T) (add x 1)))".toList (leaf 8) = some (leaf 9)
#guard runText 10000 Geb.Kernel.Tests.quadruple.toList (leaf 5) = some (leaf 20)
#guard runText 10000 Geb.Kernel.Tests.isZero.toList (leaf 0) = some (leaf 1)
#guard runText 10000 Geb.Kernel.Tests.isZero.toList (leaf 7) = some (leaf 0)
#guard runText 10000 Geb.Kernel.Tests.listCase.toList
  (RoseTree.node 9 [leaf 4, leaf 5, leaf 6]) = some (RoseTree.node 4 [leaf 5, leaf 6])
#guard runText 10000 Geb.Kernel.Tests.listCase.toList (leaf 9) = some (leaf 0)
#guard runText 10000 Geb.Kernel.Tests.factorial.toList (leaf 3) = some (leaf 6)
#guard runText 10000 Geb.Kernel.Tests.size.toList
  (RoseTree.node 1 [leaf 2, RoseTree.node 3 [leaf 4, leaf 5]]) = some (leaf 5)
#guard runText 20000 Geb.Kernel.Tests.mirror.toList
  (RoseTree.node 1 [leaf 2, RoseTree.node 3 [leaf 4, leaf 5]]) =
    some (RoseTree.node 1 [RoseTree.node 3 [leaf 5, leaf 4], leaf 2])
#guard runText 10000 Geb.Kernel.Tests.arities.toList
  (RoseTree.node 1 [leaf 2, RoseTree.node 3 [leaf 4, leaf 5]]) =
    some (RoseTree.node 2 [leaf 0, RoseTree.node 2 [leaf 0, leaf 0]])

-- Primitive edge cases include empty children, out-of-range selection and zero division.
#guard runText 2000 "(def main (lam (t T) (sub t 9)))".toList (leaf 2) = some (leaf 0)
#guard runText 2000 "(def main (lam (t T) (div t 0)))".toList (leaf 17) = some (leaf 0)
#guard runText 2000 "(def main (lam (t T) (mod t 0)))".toList (leaf 17) = some (leaf 17)
#guard runText 2000 "(def main (lam (t T) (log2 t)))".toList (leaf 256) = some (leaf 8)
#guard runText 2000 "(def main (lam (t T) (child t 1)))".toList
  (RoseTree.node 9 [leaf 4, leaf 5]) = some (leaf 5)
#guard runText 2000 "(def main (lam (t T) (child t 2)))".toList
  (RoseTree.node 9 [leaf 4, leaf 5]) = some (leaf 0)
#guard runText 4000 "(def main (lam (t T) (equal t t)))".toList
  (RoseTree.node 9 [leaf 4, leaf 5]) = some (leaf 1)
#guard runText 4000 "(def main (lam (t T) (equal t (node t (nil T)))))".toList
  (RoseTree.node 9 [leaf 4]) = some (leaf 0)
#guard runText 4000 "(def main (lam (t T) (equal t (node 10 (children t)))))".toList
  (RoseTree.node 9 [leaf 4]) = some (leaf 0)
#guard runText 4000
  "(def main (lam (t T) (equal t (node 9 (cons 4 (cons 6 (nil T)))))))".toList
  (RoseTree.node 9 [leaf 4, leaf 5]) = some (leaf 0)

-- A shared closure captures data and is applied independently to two arguments.
#guard runText 10000 "(def main (lam (t T)
  (let f (Arrow T T) (lam (x T) (add t x)) (add (f 1) (f 2)))))".toList
    (leaf 7) = some (leaf 17)

-- The text interface rejects a final definition of the wrong type and bounded exhaustion.
#guard runText 1000 "(def main (lam (t T) (pair t t)))".toList (leaf 7) = none
#guard runText 0 "(def main (lam (t T) t))".toList (leaf 7) = none

-- On raw syntax, an unreachable malformed branch demonstrates that selection is lazy.
#guard Kernel.run [] 2000
  (RoseTree.node Label.lam [tT, RoseTree.node Label.cond
    [RoseTree.node Label.quote [leaf 1], Tm.var 0, RoseTree.node Label.ref [leaf 100]]])
  (leaf 7) = some (leaf 7)

end Geb.InteractionNet.Tests

end
