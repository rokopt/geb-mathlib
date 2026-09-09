/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Scan

/-!
# The prefix encoding and its scan on samples

`Geb.BitTreeScanner.spell` computed on a few trees, and `Geb.BitTreeScanner.validBool`
checked on their spellings and on words that spell no tree: the empty word,
a leaf left open at a prefix bit and at a payload bit, a pair short of a
child, a bit after the tree, and a leaf of two payload bits left open.

## Main definitions

* `sampleTrees` — the trees the mirror spells.
* `sampleSpellings` — their spellings.
* `rejectedWords` — words that spell no tree.

## Main statements

* `sampleSpellings_eq`, `length_sampleSpellings` — the spellings and their
  lengths.
* `validBool_sampleSpellings`, `validBool_rejectedWords` — the scan accepts
  every sample spelling and rejects every rejected word, by kernel
  evaluation.

## Tags

binary tree, prefix code, scan, test
-/

@[expose] public section

open Geb Geb.BitTreeScanner

namespace BitTreeTest

/-- The trees the mirror spells. -/
def sampleTrees : List BitTree :=
  [leaf [], leaf [true, false], pair (leaf []) (leaf [true]),
   pair (pair (leaf [false]) (leaf [])) (leaf [true, true])]

/-- Their spellings. -/
def sampleSpellings : List (List Bool) := sampleTrees.map spell

/-- The spellings, as the encoding's equations give them. -/
theorem sampleSpellings_eq :
    sampleSpellings =
      [[false, false],
       [false, true, true, true, false, false],
       [true, false, false, false, true, true, false],
       [true, true, false, true, false, false, false, false, false, true, true, true, true,
        false]] :=
  rfl

/-- The sample spellings' lengths, `3 * p + 2 * m + 2` at each sample's `p` pairs
and `m` payload bits. -/
theorem length_sampleSpellings : sampleSpellings.map List.length = [2, 6, 7, 14] := rfl

/-- Words that spell no tree: the empty word, a leaf left open at a prefix bit
and at a payload bit, a pair short of a child, a bit after the tree, and a
leaf of two payload bits left open. -/
def rejectedWords : List (List Bool) :=
  [[], [false], [false, true], [true, false, false], [false, false, false],
   [false, true, true, true, false]]

/-- The scan accepts every sample spelling. -/
theorem validBool_sampleSpellings : sampleSpellings.all validBool = true := by decide

/-- The scan rejects every rejected word. -/
theorem validBool_rejectedWords : rejectedWords.all (fun w ↦ !validBool w) = true := by decide

end BitTreeTest
