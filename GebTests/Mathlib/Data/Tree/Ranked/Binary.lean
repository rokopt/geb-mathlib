/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Mathlib.Data.Tree.Ranked.Basic

import Geb.Mathlib.Data.Tree.Ranked.Binary

/-!
# The two-symbol alphabet on worked trees

The spelling of a binary tree's image under `termEquiv` against
`BinTree.print` of the tree, and the two recognizers compared on every word of
length at most eight.

## Main definitions

* `binarySample` — the tree the assertions are stated at.

## Main statements

The assertions below give the spelling of the worked tree's image, the value
`BinTree.print` gives there, and the agreement of the alphabet's scan with
`BinTree.Valid` over the enumeration.

## Tags

binary tree, ranked alphabet, preorder, equivalence, scan
-/

set_option linter.privateModule false

open RankedAlphabet.Binary

/-- The tree the assertions below are stated at: a node whose left child is a
two-leaf node and whose right child is a leaf. -/
def binarySample : BinTree := BinTree.node (BinTree.node BinTree.leaf BinTree.leaf) BinTree.leaf

/-- The equivalence carries the spelling to `BinTree.print`, at the worked
tree. -/
theorem spell_termEquiv_binarySample :
    binRanked.spell (termEquiv binarySample) = [true, true, false, false, false] := by
  decide

/-- And `BinTree.print` agrees there. -/
theorem print_binarySample :
    BinTree.print binarySample = [true, true, false, false, false] := rfl

/-- The two recognizers accept the same words: `valid_iff` at every word of
length at most eight. -/
theorem validBool_eq_decide_binTree_valid :
    (wordsUpTo 8).all (fun w ↦ binRanked.validBool w == decide (BinTree.Valid w)) = true := by
  set_option maxRecDepth 100000 in decide
