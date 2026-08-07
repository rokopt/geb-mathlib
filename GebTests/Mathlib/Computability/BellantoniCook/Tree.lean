/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Computability.BellantoniCook.Tree

/-!
# The tree recognizer on worked bitstrings

The recognizer accepting three spellings and rejecting four words — the
empty word, a word whose scan fails at a node bit, a word whose scan
succeeds at a depth other than one, and a permutation of an accepted
spelling — together with the scan on a word whose depth exceeds one.

## Main statements

The eight assertions below.

## Tags

Bellantoni-Cook, polytime, binary tree, preorder, recognizer
-/

set_option linter.privateModule false

open BellantoniCook

/-- The recognizer at its declared arity, named so that this module
references a constant of the module under test. -/
def isTreeArity : BCOf 1 0 := isTreeOf

/-- The spelling of the leaf is accepted. -/
theorem isTreeSem_print_leaf : isTreeSem ![[false]] ![] = [true] := rfl

/-- The spelling of the two-leaf node is accepted. -/
theorem isTreeSem_print_node : isTreeSem ![[true, false, false]] ![] = [true] :=
  rfl

/-- The spelling of an asymmetric tree of two nodes and three leaves is
accepted. -/
theorem isTreeSem_print_asymmetric :
    isTreeSem ![[true, true, false, false, false]] ![] = [true] := rfl

/-- The empty word is rejected: it leaves no tree on the stack. -/
theorem isTreeSem_nil : isTreeSem ![([] : List Bool)] ![] = [] := rfl

/-- A word whose node bit is read below depth two is rejected. Its depth
is one, so only the scan's failure flag separates it from an accepted
word. -/
theorem isTreeSem_underflow : isTreeSem ![[false, true, false]] ![] = [] := rfl

/-- A word whose scan succeeds at depth two is rejected: it leaves two
trees on the stack. -/
theorem isTreeSem_depth : isTreeSem ![[false, false]] ![] = [] := rfl

/-- A word with the bit counts of an accepted spelling, in the wrong
order, is rejected. Its node bit is read below depth two, and its depth
is not one. -/
theorem isTreeSem_permuted : isTreeSem ![[false, false, true]] ![] = [] := rfl

/-- The scan on a word whose depth exceeds one, separating the scan from
the recognizer. -/
theorem combSem_two_leaves :
    combSem ![[false, false]] ![] = [true, true, true] := rfl
