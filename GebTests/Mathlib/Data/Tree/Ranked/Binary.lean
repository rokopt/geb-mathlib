/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.Tree.Ranked.Binary

/-!
# The two-symbol alphabet on worked words

The spelling of a worked term, the descent's value on two spellings and its
three rejections, and the counter form of the validity scan at the words that
separate validity's two conjuncts.

## Main definitions

* `binarySample` — the term the assertions are stated at.

## Main statements

The assertions below give the worked term's spelling, the descent's value on
two spellings and its rejection of the empty, the truncated and the trailing
word, the pending count and the liveness verdict at a word failing each
conjunct of validity, and the decision of validity at an accepting and a
rejecting word.

## Tags

binary tree, ranked alphabet, preorder, descent, scan
-/

set_option linter.privateModule false

open RankedAlphabet.Binary

/-- The asymmetric term the assertions below are stated at: a node whose left
child is a two-leaf node and whose right child is a leaf. Its `size` is five,
counting leaves alongside internal nodes. -/
def binarySample : binRanked.Term := node (node leaf leaf) leaf

/-- The asymmetric term's spelling, which no symmetric term has. -/
theorem spell_binarySample :
    binRanked.spell binarySample = [true, true, false, false, false] := by
  decide

/-- A node over two leaves is spelled by a `true` bit and two `false` bits. -/
theorem spell_node_leaf_leaf :
    binRanked.spell (node leaf leaf) = [true, false, false] := by decide

/-- The descent inverts the spelling on a leaf. -/
theorem parse_spell_leaf :
    (binRanked.parse [false]).map binRanked.spell = some [false] := by decide

/-- And on the asymmetric term. -/
theorem parse_spell_binarySample :
    (binRanked.parse [true, true, false, false, false]).map binRanked.spell =
      some [true, true, false, false, false] := by decide

/-- And on a node over two leaves. -/
theorem parse_spell_node_leaf_leaf :
    (binRanked.parse [true, false, false]).map binRanked.spell =
      some [true, false, false] := by decide

/-- The descent rejects the empty word: it has nothing to read. -/
theorem parse_nil : (binRanked.parse ([] : List Bool)).map binRanked.spell = none := by
  decide

/-- The descent rejects a truncated word: the second child runs out of
input. -/
theorem parse_truncated :
    (binRanked.parse [true, false]).map binRanked.spell = none := by decide

/-- The descent rejects trailing input: it succeeds and leaves a non-empty
remainder. -/
theorem parse_trailing :
    (binRanked.parse [false, false]).map binRanked.spell = none := by decide

/-- Validity itself on the asymmetric term's spelling. -/
theorem valid_spell_binarySample :
    binRanked.Valid [true, true, false, false, false] := by decide

/-- A word failing liveness alone: its pending count is one, yet it reads a
node bit with one subterm pending. -/
theorem depth_node_at_depth_one : depth [false, true, false] = 1 := by decide

/-- The liveness half of that word. -/
theorem ok_node_at_depth_one : ok [false, true, false] = false := by decide

/-- That word is not valid, by reduction rather than through the counter
form's characterisation. -/
theorem not_valid_node_at_depth_one : ¬ binRanked.Valid [false, true, false] := by
  decide

/-- A word failing the count alone: two leaves and no node leave two
subterms pending. -/
theorem depth_two_leaves : depth [false, false] = 2 := by decide

/-- The liveness half of that word. Together with the pair at
`[false, true, false]`, validity's conjuncts are separated in both
directions. -/
theorem ok_two_leaves : ok [false, false] = true := by decide

/-- And it is not valid. -/
theorem not_valid_two_leaves : ¬ binRanked.Valid [false, false] := by decide

/-- `depth_le_length` at the empty word. -/
theorem depth_le_length_nil : depth ([] : List Bool) ≤ ([] : List Bool).length := by
  decide

/-- `depth_le_length` at a word of leaf bits only. -/
theorem depth_le_length_leaves : depth [false, false, false] ≤ 3 := by decide

/-- `depth_le_length` at a word mixing a node bit with leaf bits. -/
theorem depth_le_length_mixed : depth [true, false, false] ≤ 3 := by decide

/-- The `DecidablePred binRanked.Valid` instance accepts a valid word. -/
theorem decide_valid_leaf : decide (binRanked.Valid [false]) = true := by decide

/-- And rejects an invalid one. Its word is a node bit and a leaf bit. -/
theorem decide_not_valid_node_leaf :
    decide (binRanked.Valid [true, false]) = false := by decide
