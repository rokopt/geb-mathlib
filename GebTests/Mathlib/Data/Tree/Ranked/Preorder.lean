/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.Tree.Ranked.Preorder
public import GebTests.Mathlib.Data.Tree.Ranked.Basic

/-!
# The preorder encoding on worked terms

The spelling of `sampleNullary` and `sampleBinary`, the descent recovering
each, and the scan's three rejections: a word carrying two terms, a word
ending mid-block, and a word whose symbol has more arity than the pending
count. The scan and the descent are then compared on every word of length at
most six.

## Main statements

The assertions below give the spelling of each worked term, the descent's
value on each spelling, `Valid` on the two spellings and on the three
rejected words, and the agreement of `validBool` with `Option.isSome ∘ parse`
over the enumeration.

## Implementation notes

The descent's value is asserted through `Option.map` of the spelling rather
than against the term itself. The spelling is a `List Bool`, so the assertion
needs no `DecidableEq (WType _)` instance; the one `Geb/Mathlib/Data/W/Basic.lean`
supplies would serve, at the cost of an import and of the `FinEnum` instances
its `decide` would then reduce through.

## Tags

ranked alphabet, preorder, prefix notation, encoding, scan
-/

set_option linter.privateModule false

open RankedAlphabet

/-- A nullary term is spelled by its block alone. -/
theorem spell_sampleNullary :
    sampleAlphabet.spell sampleNullary = [false, false] := by decide

/-- A binary term is spelled by its block followed by its children's
spellings, in index order. -/
theorem spell_sampleBinary :
    sampleAlphabet.spell sampleBinary = [false, true, false, false, false, false] := by
  decide

/-- The descent recovers the nullary term. -/
theorem parse_spell_sampleNullary :
    (sampleAlphabet.parse [false, false]).map sampleAlphabet.spell =
      some [false, false] := by decide

/-- The descent recovers the binary term. -/
theorem parse_spell_sampleBinary :
    (sampleAlphabet.parse [false, true, false, false, false, false]).map
        sampleAlphabet.spell =
      some [false, true, false, false, false, false] := by decide

/-- The scan accepts a nullary term's spelling. -/
theorem valid_spell_sampleNullary : sampleAlphabet.Valid [false, false] := by decide

/-- The scan accepts a binary term's spelling. -/
theorem valid_spell_sampleBinary :
    sampleAlphabet.Valid [false, true, false, false, false, false] := by decide

/-- The scan rejects a word carrying two terms: it ends with two subterms
pending rather than one. -/
theorem not_valid_two_terms :
    ¬ sampleAlphabet.Valid [false, false, false, false] := by decide

/-- The scan rejects a word ending mid-block: its length is not a multiple of
the width, so an incomplete block is left over. -/
theorem not_valid_mid_block : ¬ sampleAlphabet.Valid [false, false, false] := by decide

/-- The scan rejects a word whose symbol has more arity than the pending
count: the binary symbol's block alone leaves nothing for it to apply to. -/
theorem not_valid_underflow : ¬ sampleAlphabet.Valid [false, true] := by decide

/-- The scan and the descent accept the same words: `valid_iff_isSome_parse`
at every word of length at most six. -/
theorem validBool_eq_isSome_parse :
    (wordsUpTo 6).all (fun w ↦
      sampleAlphabet.validBool w == (sampleAlphabet.parse w).isSome) = true := by
  set_option maxRecDepth 100000 in decide
