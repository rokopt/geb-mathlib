/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.CobhamFoldProto
public meta import Geb.Internal.Computability.CobhamFoldProto  -- shake: keep; #guard needs it

/-!
# The delimited-children algebra, at the semantic layer

The algebra from which a subterm's spelling is recovered.

`algCh` delimits each child's spelling, and the delimiting does not nest:
each level reads only the spelling half of a child's value, so a subterm's
boundary is reached by a fold.

## Main definitions

* `GebTests.CobhamFold.algCh` — the delimited-children algebra.
* `GebTests.CobhamFold.childSem` — a child's spelling, from a fold's value.
* `GebTests.CobhamFold.destSample`, `GebTests.CobhamFold.valueBounded` — the
  sample term whose children differ, and the length bound read at it.

## Main statements

* `GebTests.CobhamFold.dropEntry_algCh`,
  `GebTests.CobhamFold.takeEntry_algCh` — its value's two halves.

## Tags

Cobham, ranked tree, subterm, self-delimiting
-/

@[expose] public section

namespace GebTests.CobhamFold

open Cobham Geb.CobhamFold RankedAlphabet RankedAlphabet.Binary

/-- The delimited-children algebra: the paramorphism whose step returns its
children's spellings, each delimited. -/
def algCh (R : RankedAlphabet) : (i : Fin R.card) →
    (Fin (R.arity i) → List Bool) → List Bool :=
  algPara R fun _ g ↦ (List.ofFn fun d ↦ entryWord (g d).1).flatten

/-- Its value's second half is the spelling. -/
theorem dropEntry_algCh (R : RankedAlphabet) (t : R.Term) :
    dropEntrySem ![Term.fold R (algCh R) t] = R.spell t :=
  dropEntry_algPara R _ t

/-- Its first half is the children's spellings, each delimited, so the `j`-th
child is `Geb.CobhamFold.entryOf j` of it. -/
theorem takeEntry_algCh (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    takeEntrySem ![Term.fold R (algCh R) (Term.mk R i ch)] =
      (List.ofFn fun d ↦ entryWord (R.spell (ch d))).flatten :=
  takeEntry_algPara R _ i ch

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
