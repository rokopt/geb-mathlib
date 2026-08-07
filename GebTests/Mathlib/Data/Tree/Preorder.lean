/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.Tree.Preorder

/-!
# The preorder encoding on worked trees

The encoding and its parser on the leaf, on the two-leaf node and on an
asymmetric tree; the parser's three rejection mechanisms; and `depth` and
`ok` on words separating the two conjuncts of `Valid`, and `Valid` on an
accepted spelling and a rejected word.

## Main definitions

* `preorderSample` — the tree the assertions are stated at.

## Main statements

The fifteen assertions below.

## Tags

binary tree, preorder, prefix notation, encoding
-/

set_option linter.privateModule false

open BinTree

/-- The asymmetric tree the assertions below are stated at: a node whose
left child is a two-leaf node and whose right child is a leaf. Its `size`
is five, counting leaves alongside internal nodes. -/
def preorderSample : BinTree := node (node leaf leaf) leaf

/-- A leaf is spelled by one `false` bit. -/
theorem print_leaf_eq : print leaf = [false] := rfl

/-- A node is spelled by a `true` bit and its children's spellings. -/
theorem print_node_leaf_leaf_eq :
    print (node leaf leaf) = [true, false, false] := rfl

/-- The asymmetric tree's spelling, which no symmetric tree has. -/
theorem print_preorderSample_eq :
    print preorderSample = [true, true, false, false, false] := rfl

/-- The parser inverts the printer on the leaf. -/
theorem parse_print_leaf : parse [false] = some leaf := rfl

/-- The parser inverts the printer on the two-leaf node. -/
theorem parse_print_node_leaf_leaf :
    parse [true, false, false] = some (node leaf leaf) := rfl

/-- The parser inverts the printer on the asymmetric tree. -/
theorem parse_print_preorderSample :
    parse [true, true, false, false, false] = some preorderSample := rfl

/-- The parser rejects the empty word: the descent has nothing to read. -/
theorem parse_nil : parse ([] : List Bool) = none := rfl

/-- The parser rejects a truncated word: the second child's descent runs
out of input. -/
theorem parse_truncated : parse [true, false] = none := rfl

/-- The parser rejects trailing input: the descent succeeds and leaves a
non-empty remainder. -/
theorem parse_trailing : parse [false, false] = none := rfl

/-- A word failing `ok` alone: its depth is one, yet it reads a node bit
at depth one. -/
theorem depth_node_at_depth_one : depth [false, true, false] = 1 := rfl

/-- The `ok` half of that word. -/
theorem ok_node_at_depth_one : ok [false, true, false] = false := rfl

/-- A word failing the depth conjunct alone: two leaves and no node leave
two trees on the stack. -/
theorem depth_two_leaves : depth [false, false] = 2 := rfl

/-- The `ok` half of that word. Together with the two above, the
conjuncts of `Valid` are separated in both directions. -/
theorem ok_two_leaves : ok [false, false] = true := rfl

/-- `Valid` itself on the asymmetric tree's spelling. -/
theorem valid_print_preorderSample :
    Valid [true, true, false, false, false] := ⟨rfl, rfl⟩

/-- `Valid` itself on the word whose depth conjunct fails. -/
theorem not_valid_two_leaves : ¬ Valid [false, false] :=
  fun h ↦ absurd h.2 (by decide)
