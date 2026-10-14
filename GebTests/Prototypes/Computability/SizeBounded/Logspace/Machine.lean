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
each worked word. The run is evaluated through the transition function and
from the initial state of the machine's program `machineProg`: the machine's
own transition is selected by choice in CSLib and does not evaluate, and
`machine_tr` and `toCfg_execStep_iterate_eq_runFrom` identify the evaluated run
with the machine's.

## Main definitions

* `runTail` — the output of a run from a word, stepped until it halts.

## Main statements

The run halts within the machine's step bound and its output on each word is
the word's tail.

## Tags

logspace, Turing machine, compilation
-/

set_option linter.privateModule false

open Geb.SizeBounded.Machine Geb.SizeBounded.Logspace.Machine
open Geb.SizeBounded.Logspace (tailL)

/-- The machine's output on a word, run to its halt within its step bound, by the
transition function of the machine's program from its initial state. -/
def runTail (w : List Bool) : Option (List Bool) :=
  stepUntilHalt (machineProg tailL).tr (time tailL w.length + 1)
    (ExecCfg.init (machineProg tailL).q₀ w) []

#guard runTail [true, false, true, true, false] = some [false, true, true, false]
#guard runTail [] = some []
#guard runTail [true] = some []
#guard runTail [false, true] = some [true]
