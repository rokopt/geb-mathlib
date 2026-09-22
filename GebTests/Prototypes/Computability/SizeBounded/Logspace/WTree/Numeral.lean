/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree -- shake: keep; #guard needs it
public import Geb.Prototypes.Computability.SizeBounded.Sharing -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Sharing -- shake: keep; #guard needs it

/-!
# The binary numerals and their scanner on worked words

The code of small numbers, the reader on the code followed by a suffix, and
the scanner on words holding a code at a position, as the scanner of states
and as the expressions evaluated with sharing.

## Main definitions

* `numeralWord` — a word with a coded number at a position, followed by a
  suffix.
* `numAt` — the acceptance, end position and bit at an index, from the
  expressions evaluated with sharing.

## Main statements

`numAt_eq` identifies the shared expressions with the native scanner.

The codes of zero to four are as worked by hand; the reader inverts the code
on every number below twenty; the scanner accepts each coded number at its
position, ending after it with its bits, and rejects a word whose numeral is
cut short, one whose bits end in `false`, and one with no numeral at the
position. The expression sweeps use the scanner's correctness equalities;
small malformed inputs also exercise the interpreter directly.

## Tags

binary numeral, scanner, logspace
-/

set_option linter.privateModule false

open Geb.SizeBounded.Logspace.WTree.Numeral Geb.SizeBounded.Logspace.WTree.NumExpr

#guard natCode 0 = [true]

#guard natCode 1 = [false, true, false, true]

#guard natCode 2 = [false, true, true, false, true]

#guard natCode 3 = [false, true, true, true, true]

#guard natCode 4 = [false, false, true, false, false, false, false, true]

#guard (List.range 20).all fun n ↦
  readNatCode (natCode n ++ [true, false]) == some (n, [true, false])

/-- A word with a coded number at a position, followed by a suffix. -/
def numeralWord (pre : List Bool) (n : ℕ) (suf : List Bool) : List Bool := pre ++ natCode n ++ suf

#guard (List.range 20).all fun n ↦
  let w := numeralWord [true, true] n [false]
  let x := nrun 2 0 w
  x.mode == .done && x.ok && x.endPos == 2 + (natCode n).length && x.hit == n.bits.getD 0 false

#guard (List.range 20).all fun n ↦
  let w := numeralWord [] n []
  (List.range 6).all fun i ↦ (nrun 0 i w).hit == n.bits.getD i false

-- The numeral of four cut short after its size field.
#guard (nrun 0 0 [false, false, true, false, false, false]).mode != NMode.done

-- Bits ending in `false` are not canonical.
#guard (nrun 0 0 [false, true, true, true, false]).ok == false

-- No numeral at the position: the word ends before it.
#guard (nrun 3 0 [true, true]).mode != NMode.done

/-- The acceptance, the end position and the bit at an index, from the
expressions evaluated with sharing. -/
def numAt (w : List Bool) (tp i : ℕ) : List Bool × List Bool × List Bool :=
  (numOk.1.semVec ![w, w.drop tp, w.drop i], numEnd.1.semVec ![w, w.drop tp, w.drop i],
    numHit.1.semVec ![w, w.drop tp, w.drop i])

#guard numAt [true] 0 0 = ([true], [], [])

/-- The shared expressions agree with the native scanner, with counters
clipped to the input length as their end-segment representation requires. -/
theorem numAt_eq (w : List Bool) (tp i : ℕ) :
    numAt w tp i =
      let s := nrun (min tp w.length) (min i w.length) w
      (Geb.SizeBounded.Logspace.WTree.boolWord (decide (s.mode = .done) && s.ok),
        w.drop s.endPos, Geb.SizeBounded.Logspace.WTree.boolWord s.hit) := by
  have drop_min (n : ℕ) : w.drop n = w.drop (min n w.length) := by
    by_cases h : n ≤ w.length
    · rw [Nat.min_eq_left h]
    · have hl : w.length ≤ n := by omega
      rw [Nat.min_eq_right hl, List.drop_length, List.drop_eq_nil_of_le hl]
  simp only [numAt, Geb.SizeBounded.SOf.semVec_eq, drop_min tp, drop_min i]
  change (numOk.sem ![w, w.drop (min tp w.length), w.drop (min i w.length)],
    numEnd.sem ![w, w.drop (min tp w.length), w.drop (min i w.length)],
    numHit.sem ![w, w.drop (min tp w.length), w.drop (min i w.length)]) = _
  rw [sem_numOk _ _ _ (Nat.min_le_right _ _) (Nat.min_le_right _ _),
    sem_numEnd _ _ _ (Nat.min_le_right _ _) (Nat.min_le_right _ _),
    sem_numHit _ _ _ (Nat.min_le_right _ _) (Nat.min_le_right _ _)]

example : ((List.range 12).all fun n ↦
  let w := numeralWord [true, true] n [false]
  numAt w 2 0 == ([true], [false], if n.bits.getD 0 false then [true] else [])) = true := by
  simp only [numAt_eq]
  decide

example : ((List.range 12).all fun n ↦
  (List.range 5).all fun i ↦
    (numAt (numeralWord [] n []) 0 i).2.2 ==
      if n.bits.getD i false then [true] else []) = true := by
  simp only [numAt_eq]
  decide

#guard (numAt [false, false, true, false, false, false] 0 0).1 == []

#guard (numAt [false, true, true, true, false] 0 0).1 == []

#guard (numAt [true, true] 3 0).1 == []
