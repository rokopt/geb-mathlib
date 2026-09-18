/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree -- shake: keep; #guard needs it

/-!
# The Elias-length tree recognizer on worked bitstrings

The counters after the encoding of a leaf, and the recognizer on the empty
leaf, a leaf with a payload, a fork of two leaves, the empty word, a lone
fork bit, an incomplete fork, a leaf followed by a trailing leaf, and a
header cut short.

## Main statements

The recognizer returns `[true]` on each encoding and the empty word on each
non-encoding, agreeing with `Geb.BitTree.Elias.validBool` at every worked
word.

## Tags

logspace, Elias delta code, binary tree, recognizer
-/

set_option linter.privateModule false

open Geb.BitTree (leaf fork)
open Geb.BitTree.Elias (encode)
open Geb.SizeBounded.Logspace.EliasTree

/-- The recognizer, named so that this module references a constant of the
module under test. -/
def isEliasTreeArity : Geb.SizeBounded.Logspace.LOf 1 := isEliasTree

/-- A leaf with a two-bit payload. -/
def leafTwo : Geb.BitTree.Tree := leaf [true, false]

#guard encode leafTwo = [false, false, true, true, false, true, false]

/-- After the encoding of the empty leaf, one leaf is complete and the phase
is the completed one. -/
#guard run (encode (leaf [])) = ⟨.done, 0, 1, 0, 0, 0⟩

/-- After a leaf with a two-bit payload, the count has reached the bound
three, one plus the payload's length. -/
#guard run (encode leafTwo) = ⟨.done, 0, 1, 3, 3, 3⟩

#guard isEliasTree.sem ![encode (leaf [])] = [true]

#guard isEliasTree.sem ![encode leafTwo] = [true]

#guard isEliasTree.sem ![encode (fork (leaf []) leafTwo)] = [true]

#guard isEliasTree.sem ![encode (fork (fork leafTwo (leaf [true])) (leaf []))] = [true]

#guard isEliasTree.sem ![[]] = []

#guard isEliasTree.sem ![[true]] = []

#guard isEliasTree.sem ![[true, false, true]] = []

#guard isEliasTree.sem ![[false, true, false, true]] = []

#guard isEliasTree.sem ![[false, false, true]] = []

/-- The worked words. -/
def workedWords : List (List Bool) :=
  [encode (leaf []), encode leafTwo, encode (fork (leaf []) leafTwo), [], [true],
    [true, false, true], [false, true, false, true], [false, false, true]]

#guard workedWords.all fun w ↦
  isEliasTree.sem ![w] == if Geb.BitTree.Elias.validBool w then [true] else []
