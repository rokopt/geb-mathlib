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
a leaf's gamma code left short of its one, of its digits and of its payload, a
pair short of a child, and a bit after the tree.

## Main definitions

* `sampleTrees` — the trees the mirror spells.
* `sampleSpellings` — their spellings.
* `rejectedWords` — words that spell no tree.

## Main statements

* `sampleSpellings_eq`, `length_sampleSpellings` — the spellings and their
  lengths.
* `gamma_five`, `gamma_one` — the gamma code at a two-digit and at the
  one-digit number.
* `validBool_sampleSpellings`, `validBool_rejectedWords` — the scan accepts
  every sample spelling and rejects every rejected word, by kernel
  evaluation.

## Tags

binary tree, prefix code, Elias gamma code, scan, test
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

/-- The spellings, as the encoding's equations give them: a leaf is `false`, the
gamma code of its length plus one, and its bits. -/
theorem sampleSpellings_eq :
    sampleSpellings =
      [[false, true],
       [false, false, true, true, true, false],
       [true, false, true, false, false, true, false, true],
       [true, true, false, false, true, false, false, false, true, false, false, true, true,
        true, true]] :=
  rfl

/-- The sample spellings' lengths, `2 * p + 1 + m` plus the gamma codes at each
sample's `p` pairs and `m` payload bits. -/
theorem length_sampleSpellings : sampleSpellings.map List.length = [2, 6, 8, 15] := rfl

/-- The gamma code of five: two zeros, then its digits `101`. -/
theorem gamma_five : gamma 5 = [false, false, true, false, true] := rfl

/-- The gamma code of one: no zeros, then its digit. -/
theorem gamma_one : gamma 1 = [true] := rfl

/-- Words that spell no tree: the empty word, a leaf's gamma code left short of
its one, of its digits and of its payload, a pair short of a child, and a bit
after the tree. -/
def rejectedWords : List (List Bool) :=
  [[], [false], [false, false], [false, false, true], [false, false, true, false],
   [true, false, true], [false, true, false]]

/-- The scan accepts every sample spelling. -/
theorem validBool_sampleSpellings : sampleSpellings.all validBool = true := by decide

/-- The scan rejects every rejected word. -/
theorem validBool_rejectedWords : rejectedWords.all (fun w ↦ !validBool w) = true := by decide

end BitTreeTest
