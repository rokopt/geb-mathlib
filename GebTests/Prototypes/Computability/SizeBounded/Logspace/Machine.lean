/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine -- shake: keep; #guard needs it
public import Geb.Prototypes.Computability.SizeBounded.Machine.Exec -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Machine.Exec -- shake: keep; #guard needs it
public import GebTests.Prototypes.Computability.SizeBounded.Logspace -- shake: keep; #guard needs it
public meta import GebTests.Prototypes.Computability.SizeBounded.Logspace -- shake: keep; #guard needs it

/-!
# The tail's machine on worked bitstrings

The compiled machine of the tail, stepped until it halts, emits the tail of
each worked word.

## Main statements

The machine halts within its step bound and its output on each word is the
word's tail.

## Tags

logspace, Turing machine, compilation
-/

set_option linter.privateModule false

open Geb.SizeBounded.Machine Geb.SizeBounded.Logspace.Machine

/-- The tail's machine, named so that this module references a constant of the
module under test. -/
def tailMachine := machine tailL

/-- The machine's output on a word, run to its halt within its step bound. -/
def runTail (w : List Bool) : Option (List Bool) :=
  stepUntilHalt tailMachine (time tailL w.length + 1) (ExecCfg.init tailMachine w) []

#guard runTail [true, false, true, true, false] = some [false, true, true, false]
#guard runTail [] = some []
#guard runTail [true] = some []
#guard runTail [false, true] = some [true]
