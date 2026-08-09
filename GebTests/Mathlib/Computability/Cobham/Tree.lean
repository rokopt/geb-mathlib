/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Computability.Cobham.Tree

/-!
# The preorder stack scan and the recognizer on worked bitstrings

The scan on the empty word, on the spelling of the leaf, on the spelling of the
two-leaf node, on a word whose depth exceeds one, and on a word that reads a
node bit below depth two, together with the recognizer built on the scan: on
the spelling of the leaf, on the spelling of the two-leaf node, on a word
failing `ok`, and on a word that is `ok` but leaves the wrong depth.

## Main statements

The assertions below.

## Tags

Cobham, bounded recursion on notation, binary tree, preorder, recognizer
-/

set_option linter.privateModule false

open Cobham

/-- The scan at its declared arity, named so that this module references a
constant of the module under test. -/
def combArity : COf 1 := combOf

/-- The recognizer at its declared arity. -/
def isTreeArity : COf 1 := isTreeOf

/-- The meaning `combSem` reads at the raw tree is the meaning the expression
carries: the transport along `fst_eval` that `C.eval` performs does not
obstruct reduction, so a consumer reaching the scan through `combOf` gets the
function every statement of the module is about. -/
theorem combSem_eq_eval : transport combOf.2 combOf.1.eval = combSem := rfl

/-- The meaning `isTreeSem` reads at the raw tree is the meaning the
recognizer carries, as `combSem_eq_eval` for the scan. -/
theorem isTreeSem_eq_eval : transport isTreeOf.2 isTreeOf.1.eval = isTreeSem := rfl

/-- The empty word has depth zero and satisfies `ok`, so the scan returns the
offset depth `[true]`. -/
theorem combSem_empty : combSem ![[]] = [true] := rfl

/-- The spelling of the leaf leaves one tree on the stack. Transposing the two
step children of `combRaw` would read the leaf bit as a node bit, whose guard
is the base value with two bits dropped and so empty, returning `[false]`. -/
theorem combSem_leaf : combSem ![[false]] = [true, true] := rfl

/-- The spelling of the two-leaf node leaves one tree on the stack. Its scan
exercises both steps in sequence, the leaf bits raising the offset depth to
three and the node bit lowering it to two, so the value at each step depends on
the one before. Under the same transposition it returns `[false]`. -/
theorem combSem_node : combSem ![[true, false, false]] = [true, true] := rfl

/-- Two leaf bits leave two trees on the stack, which the scan reports as an
offset depth of three. -/
theorem combSem_two_leaves : combSem ![[false, false]] = [true, true, true] := rfl

/-- A word whose node bit is read below depth two fails `ok`, and the scan
returns the absorbing failure flag. Its depth is one, so only the flag
separates it from the spelling of the leaf. -/
theorem combSem_underflow : combSem ![[false, true, false]] = [false] := rfl

/-- The failure flag is absorbing: a later leaf bit does not restore a live
value. -/
theorem combSem_underflow_absorbing :
    combSem ![[false, false, true, false]] = [false] := rfl

/-- The spelling of the leaf is accepted: its scan leaves a single tree on the
stack. -/
theorem isTreeSem_leaf : isTreeSem ![[false]] = [true] := rfl

/-- The spelling of the two-leaf node is accepted. -/
theorem isTreeSem_node : isTreeSem ![[true, false, false]] = [true] := rfl

/-- A word whose node bit is read below depth two is rejected: its scan fails
`ok` and returns the absorbing failure flag, whose predecessor is empty and so
not of length one. -/
theorem isTreeSem_underflow : isTreeSem ![[false, true, false]] = [] := rfl

/-- Two leaf bits satisfy `ok` but leave two trees on the stack rather than
one, so the word is rejected. This separates `eqOne`, tested on the scan's
predecessor, from a test that merely checks the predecessor is non-empty,
which this word's predecessor also satisfies. -/
theorem isTreeSem_wrong_depth : isTreeSem ![[false, false]] = [] := rfl
