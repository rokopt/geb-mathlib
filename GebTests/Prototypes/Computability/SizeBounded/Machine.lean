/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Machine -- shake: keep; #guard needs it
public import Geb.Prototypes.Computability.SizeBounded.BitTree -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.BitTree -- shake: keep; #guard needs it

/-!
# The bit-tree recognizer's machine on worked bitstrings

The compiled machine of the recognizer, stepped until it halts, emits the
recognizer's value on each of the worked words of the recognizer's test module.

## Main statements

The machine halts within its step bound and its output on each word is the
recognizer's value there: `[true]` on an encoding, `[]` otherwise.

## Tags

non-size-increasing, Turing machine, compilation, recognizer
-/

set_option linter.privateModule false

open Geb.SizeBounded Geb.SizeBounded.Machine Turing MultiTapeTM

/-- The recognizer's machine, named so that this module references a constant of
the module under test. -/
def bitTreeMachine := machine isBitTree

/-- The machine's output on a word, run to its halt within its step bound. -/
def run (w : List Bool) : Option (List Bool) :=
  stepUntilHalt bitTreeMachine (time isBitTree w.length + 1) (ExecCfg.init bitTreeMachine w) []

/-- The recognizer's value on a word. -/
def expected (w : List Bool) : Option (List Bool) :=
  some (if Geb.BitTree.validBool w then [true] else [])

#guard run [false, false] = expected [false, false]
#guard run [false, true, true, false] = expected [false, true, true, false]
#guard run [true, false, false, false, false] = expected [true, false, false, false, false]
#guard run [] = expected []
#guard run [true] = expected [true]
#guard run [true, false, false] = expected [true, false, false]
#guard run [false, false, false, false] = expected [false, false, false, false]
#guard run [true, true, true] = expected [true, true, true]
