/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelGraph
public import Geb.Prototypes.Kernel.Modules
public import GebTests.Prototypes.Kernel
public meta import Geb.Prototypes.InteractionNet.KernelGraph -- shake: keep
public meta import Geb.Prototypes.Kernel.Modules -- shake: keep
public meta import GebTests.Prototypes.Kernel -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Compiler-to-graph execution tests

Textual kernel programs run through the finite graph compiler, partner-array reducer and
whole-tree read-back. The cases exercise empty and nested data, constructor allocation,
calls, copying, erasure and bounded exhaustion. Separate wire-only configurations check
that graph assembly retains closed wire components.

## Main definitions

* {lit}`runText` — parse a kernel program and execute its last definition as a graph.

## Tags

interaction net, graph compiler, kernel, runtime, regression test, read-back
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Tests.CompilerGraph

open Geb.Kernel

/-- Execute the final definition using graph compilation and partner-array reduction. -/
def runText (steps : ℕ) (text : List Char) (input : Tree) : Option Tree := do
  let ds ← readProgram text
  let P := ds.map Prod.snd
  let G ← load P
  if (← G.getLast?).1 = tArrow tT tT then
    Kernel.graphRun P steps (← P.getLast?) input
  else none

#guard runText 0 "(def id (lam (x T) x))".toList (leaf 7) = none
#guard runText 40 "(def id (lam (x T) x))".toList (leaf 7) = some (leaf 7)
#guard runText 100 "(def id (lam (x T) x))".toList
  (RoseTree.node 3 [leaf 4, RoseTree.node 5 [leaf 6]]) =
    some (RoseTree.node 3 [leaf 4, RoseTree.node 5 [leaf 6]])
#guard runText 100 "(def add1 (lam (x T) (add x 1)))".toList (leaf 8) = some (leaf 9)
#guard runText 200 "(def twice (lam (x T) (add x x)))".toList (leaf 8) = some (leaf 16)
#guard runText 200 Geb.Kernel.Tests.isZero.toList (leaf 0) = some (leaf 1)
#guard runText 200 Geb.Kernel.Tests.isZero.toList (leaf 7) = some (leaf 0)
#guard runText 400 "(def main (lam (t T)
  (let f (Arrow T T) (lam (x T) (add t x)) (add (f 1) (f 2)))))".toList
    (leaf 7) = some (leaf 17)
#guard runText 3000 Geb.Kernel.Tests.size.toList
  (RoseTree.node 1 [leaf 2, leaf 3]) = some (leaf 3)
#guard runText 3000 Geb.Kernel.Tests.mirror.toList
  (RoseTree.node 1 [leaf 2, leaf 3]) = some (RoseTree.node 1 [leaf 3, leaf 2])

/-- An equation whose two occurrences form one closed wire. -/
def wireLoop : Config (fun _ : Fin 0 ↦ 0) := ⟨[], [(Term.var 0, Term.var 0)], 1⟩

/-- The closed-wire equation uses its name exactly twice. -/
theorem wireLoop_closed : wireLoop.Closed := by
  intro x hx
  have hx : x = 0 := by simpa [wireLoop, Config.names] using hx
  subst x
  rfl

#guard (wireLoop.toFiniteNet wireLoop_closed).1 = 0
#guard (wireLoop.toFiniteNet wireLoop_closed).2.2.loops = 1

end Geb.InteractionNet.Tests.CompilerGraph

end
