/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.CobhamFoldProto
public meta import Geb.Internal.Computability.CobhamFoldProto  -- shake: keep; #guard needs it

/-!
# A subterm's spelling, on samples

`GebTests.CobhamFold.childSem` at the two-symbol alphabet, and the fold's
value read against the term's node count.

## Main definitions

* `GebTests.CobhamFold.childSem` — a child's spelling, from a fold's value.
* `GebTests.CobhamFold.destSample`, `GebTests.CobhamFold.valueBounded` — the
  sample term whose children differ, and the length bound read at it.

## Tags

Cobham, ranked tree, subterm
-/

@[expose] public section

namespace GebTests.CobhamFold

open Cobham Geb.CobhamFold RankedAlphabet RankedAlphabet.Binary

/-- The `j`-th child's spelling, read from a term's fold value. -/
def childSem (R : RankedAlphabet) (j : ℕ) (t : R.Term) : List Bool :=
  stepWord (entryOf j) (takeEntrySem ![Term.fold R (algCh R) t])

/-- A sample term whose two children differ. -/
def destSample : binRanked.Term := node leaf (node leaf leaf)

#guard binRanked.spell destSample = [true, false, true, false, false]
#guard childSem binRanked 0 destSample = [false]
#guard childSem binRanked 1 destSample = [true, false, false]

/-- At `binRanked`, the fold's value stays within six times the term's node
count. The factor is this alphabet's; no general bound is proved here. -/
def valueBounded (t : binRanked.Term) : Bool :=
  (Term.fold binRanked (algCh binRanked) t).length ≤ 6 * t.size

#guard valueBounded leaf
#guard valueBounded (node leaf leaf)
#guard valueBounded destSample
#guard valueBounded (node (node leaf leaf) (node leaf leaf))

end GebTests.CobhamFold
