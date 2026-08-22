/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.CobhamFoldProto
public meta import Geb.Prototypes.Computability.CobhamFoldProto  -- shake: keep; #guard needs it

/-!
# The term algebra's destructor, on samples

`Geb.CobhamFold.childSem` at the two-symbol alphabet, checked by `#guard`
against a term whose two children differ, and the fold's value read against
the term's node count.

The samples exercise the semantic layer.
`Geb.CobhamFold.stepWord_childOf` identifies the expression with it
symbolically, so no sample forces the readout's `Cobham.casesOf` tree, whose
branch family is `2 ^ Geb.CobhamFold.readoutWidthV R` wide.

## Main definitions

* `GebTests.CobhamFold.destSample` — a term whose two children differ.
* `GebTests.CobhamFold.valueBounded` — the length bound read at that
  alphabet.

## Tags

Cobham, ranked tree, destructor, subterm, test
-/

@[expose] public section

namespace GebTests.CobhamFold

open Geb.CobhamFold RankedAlphabet RankedAlphabet.Binary

/-- A sample term whose two children differ. -/
def destSample : binRanked.Term := node leaf (node leaf leaf)

#guard binRanked.spell destSample = [true, false, true, false, false]
#guard childSem binRanked 0 destSample = [false]
#guard childSem binRanked 1 destSample = [true, false, false]

/-- At `binRanked`, the fold's value stays within six times the term's node
count. `Geb.CobhamFold.length_fold_algCh_le` proves the general bound
`chGrowth R * (R.width * t.size)`, which is twelve times the node count here;
the factor six is this alphabet's and is checked on the terms below rather
than proved. -/
def valueBounded (t : binRanked.Term) : Bool :=
  (Term.fold binRanked (algCh binRanked) t).length ≤ 6 * t.size

#guard valueBounded leaf
#guard valueBounded (node leaf leaf)
#guard valueBounded destSample
#guard valueBounded (node (node leaf leaf) (node leaf leaf))

end GebTests.CobhamFold

end
