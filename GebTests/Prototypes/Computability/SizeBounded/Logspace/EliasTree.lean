/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree -- shake: keep; #guard needs it
public import Geb.Prototypes.Computability.SizeBounded.Sharing -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Sharing -- shake: keep; #guard needs it

/-!
# The Elias-length tree recognizer on worked bitstrings

The counters after the encodings of leaves and forks and after words that
are not encodings, agreeing with `Geb.BitTree.Elias.validBool` on every
worked word; the recognizer on the empty leaf, the empty word, a lone fork
bit, a lone leaf tag and two fork bits; and its shared meaning on every
worked word.

## Main statements

The counters end in the completed phase exactly on the encodings, the
recognizer returns `[true]` on the empty leaf and the empty word on each
non-encoding, and its shared meaning agrees with the decoder on every worked
word.

## Implementation notes

The words the reference interpretation is evaluated on have at most two
bits: the algebra's recursion `Geb.SizeBounded.evalSRN` recomputes a register
of the previous stage at every reference a step makes to it, so the evaluation
of an expression whose steps read several registers is exponential in the
word's length. The shared interpretation `Geb.SizeBounded.SOf.semVec`
evaluates each stage once and is run on the longer worked words.

## Tags

logspace, Elias delta code, binary tree, recognizer
-/

set_option linter.privateModule false

open Geb.BitTree (leaf fork)
open Geb.BitTree.Elias (encode validBool)
open Geb.SizeBounded.Logspace.EliasTree

/-- The recognizer, named so that this module references a constant of the
module under test. -/
def isEliasTreeArity : Geb.SizeBounded.Logspace.LOf 1 := isEliasTree

/-- A leaf with a one-bit payload: the tag, the delta code of one, and the
bit. -/
def leafOne : Geb.BitTree.Tree := leaf [true]

#guard encode leafOne = [false, false, true, false, false, true]

-- After the encoding of the empty leaf, one leaf is complete and the phase is
-- the completed one.
#guard run (encode (leaf [])) = ⟨.done, 0, 1, 0, 0, 0⟩

-- After a leaf with a one-bit payload, the count has reached the bound two,
-- one plus the payload's length.
#guard run (encode leafOne) = ⟨.done, 0, 1, 2, 2, 2⟩

-- After a fork of two leaves, the leaves exceed the forks by one.
#guard run (encode (fork (leaf []) leafOne)) = ⟨.done, 1, 2, 2, 2, 2⟩

/-- The worked words: the encodings of the empty leaf, of a leaf with a payload,
of a fork of two leaves and of a fork of forks, and the empty word, a lone fork
bit, an incomplete fork, a leaf followed by a trailing leaf, a header cut short
and a payload cut short. -/
def workedWords : List (List Bool) :=
  [encode (leaf []), encode leafOne, encode (fork (leaf []) leafOne),
    encode (fork (fork leafOne (leaf [true, false])) (leaf [])), [], [true],
    [true, false, true], [false, true, false, true], [false, false, true],
    [false, false, true, false, false]]

#guard workedWords.all fun w ↦ decide ((run w).phase = .done) == validBool w

#guard isEliasTree.sem ![encode (leaf [])] = [true]

#guard isEliasTree.sem ![[]] = []

#guard isEliasTree.sem ![[true]] = []

#guard isEliasTree.sem ![[false]] = []

#guard isEliasTree.sem ![[true, true]] = []

#guard workedWords.all fun w ↦ decide (isEliasTree.1.semVec ![w] = [true]) == validBool w
