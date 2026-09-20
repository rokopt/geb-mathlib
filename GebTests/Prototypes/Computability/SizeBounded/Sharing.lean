/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Sharing -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Sharing -- shake: keep; #guard needs it
public import Geb.Prototypes.Computability.SizeBounded.BitTree -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.BitTree -- shake: keep; #guard needs it

/-!
# The evaluator with sharing on worked bitstrings

The shared meaning of the bit-tree recognizer agrees with
`Geb.BitTree.validBool` on the encodings of trees of a few dozen nodes and on
their corruptions, words on which the reference interpretation does not
return in practice.

## Main statements

The recognizer's shared meaning is `[true]` on each encoding and the empty
word on each corruption.

## Tags

non-size-increasing, evaluator, sharing, binary tree, recognizer
-/

set_option linter.privateModule false

open Geb.BitTree (leaf fork encode validBool)
open Geb.SizeBounded

/-- The recognizer's shared meaning, named so that this module references a
constant of the module under test. -/
def isBitTreeShared : Cobham.Sem 1 := isBitTree.semVec

/-- A tree of five leaves. -/
def small : Geb.BitTree.Tree :=
  fork (fork (leaf [true, false, true]) (leaf []))
    (fork (leaf [false, false, true, true, true]) (fork (leaf [true]) (leaf [true, true, false])))

/-- A tree of forty leaves. -/
def large : Geb.BitTree.Tree :=
  fork (fork small (fork small small)) (fork (fork small small) (fork small (fork small small)))

/-- The worked words: the two encodings, each cut short by a bit and each
extended by a bit. -/
def workedWords : List (List Bool) :=
  [encode small, encode large, (encode small).dropLast, (encode large).dropLast,
    encode small ++ [true], encode large ++ [false]]

#guard (encode large).length > 200

#guard workedWords.all fun w ↦ decide (isBitTreeShared ![w] = [true]) == validBool w
