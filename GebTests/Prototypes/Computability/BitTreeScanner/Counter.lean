/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Counter

/-!
# The redundant counter on samples

`Geb.BitTreeScanner.Redundant.inc` and `Geb.BitTreeScanner.Redundant.dec` computed on short
counters, the replay `Geb.BitTreeScanner.treeAt` on a spelling, and the counter's
value against the scan's pending count, by kernel evaluation.

## Main definitions

* `sampleCounters` — counters the mirror increments and decrements.
* `sampleWord` — a spelling the mirror replays.

## Main statements

* `inc_sampleCounters`, `dec_sampleCounters` — the increment and the
  decrement on each sample counter.
* `treeAt_prefixes` — the counter after each prefix of the sample word, and
  its value against the scan's count.

## Tags

binary counter, redundant number system, test
-/

@[expose] public section

open Geb Geb.BitTreeScanner Geb.BitTreeScanner.Redundant

namespace CounterTest

/-- Counters the mirror increments and decrements: the empty counter, a lone
one, a run of twos, a run of zeros under a one, and mixed digits. -/
def sampleCounters : List (List Digit) :=
  [[], [1], [2, 2], [0, 0, 1], [1, 2, 0, 1]]

/-- The increment on each sample counter: a run of twos becomes ones under a
new one, and a digit below two is raised. -/
theorem inc_sampleCounters :
    sampleCounters.map inc = [[1], [2], [1, 1, 1], [1, 0, 1], [2, 2, 0, 1]] := rfl

/-- The decrement on each sample counter: the empty counter stays, a lone one
is erased, a run of zeros becomes ones and the one above is lowered, its
leading zero erased. -/
theorem dec_sampleCounters :
    sampleCounters.map dec = [[], [], [1, 2], [1, 1], [0, 2, 0, 1]] := rfl

/-- A spelling the mirror replays: a pair of a pair of two empty leaves and an
empty leaf. -/
def sampleWord : List Bool := spell (pair (pair (leaf []) (leaf [])) (leaf []))

/-- The counter after each prefix of the sample word, at the word's bound,
denotes the scan's pending count there. -/
theorem treeAt_prefixes :
    (List.range (sampleWord.length + 1)).all (fun k ↦
      value (treeAt (bound sampleWord) (sampleWord.take k)) ==
        (scanAt (bound sampleWord) (sampleWord.take k)).count) = true := by
  decide

end CounterTest
