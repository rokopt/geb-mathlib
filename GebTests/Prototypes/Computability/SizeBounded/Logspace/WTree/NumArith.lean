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
# The comparisons of numerals on worked words

The equality test, the order test, the reading into a counter and the sum
check, evaluated with sharing on words holding three coded numbers.

## Main definitions

* `threeWord` — a word holding three coded numbers, with the positions of the
  second and third.
* `arithAt` — the four operations evaluated with sharing at the three
  positions.

## Main statements

On three triples of small numbers, the equality and order tests agree with
the numbers' equality and order, the reading is the word dropped by the first
number, and the sum check with a carry in agrees with the sum, by `#guard`.
The evaluation with sharing of a fold whose step evaluates a scan is slow,
which keeps the words short.

## Tags

binary numeral, comparison, addition, logspace
-/

set_option linter.privateModule false

open Geb.SizeBounded.Logspace.WTree.Numeral Geb.SizeBounded.Logspace.WTree.NumArith
  Geb.SizeBounded.Logspace.WTree.NumSum

/-- A word holding three coded numbers after a leading bit, with the positions
of the second and third. -/
def threeWord (a b c : ℕ) : List Bool × ℕ × ℕ :=
  (true :: (natCode a ++ natCode b ++ natCode c), 1 + (natCode a).length,
    1 + (natCode a).length + (natCode b).length)

/-- The four operations evaluated with sharing at the three positions: the
equality of the first two, their order, the reading of the first, and the sum
check of the third against the first two with the given carry in. -/
def arithAt (a b c : ℕ) (cin : Bool) : List Bool × List Bool × List Bool × List Bool :=
  let w := (threeWord a b c).1
  let env := ![w, w.drop 1, w.drop (threeWord a b c).2.1, w.drop (threeWord a b c).2.2]
  (natEq.1.semVec env, natLt.1.semVec env, natValue.1.semVec env, (natSum cin).1.semVec env)

-- Equal numbers, the third their sum.
#guard arithAt 1 1 2 false == ([true], [], (threeWord 1 1 2).1.drop 1, [true])

-- The first below the second; the third is not their sum with a carry in.
#guard arithAt 1 2 3 true == ([], [true], (threeWord 1 2 3).1.drop 1, [])

-- The first above the second; the third is their sum with a carry in.
#guard arithAt 2 1 4 true == ([], [], (threeWord 2 1 4).1.drop 2, [true])
