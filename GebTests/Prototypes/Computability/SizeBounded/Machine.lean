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
The run is evaluated through the transition function and from the initial state
of the machine's program `machineProg`: the machine's own transition is selected
by choice in CSLib and does not evaluate, and `machine_tr` and
`toCfg_execStep_iterate_eq_runFrom` identify the evaluated run with the
machine's.

## Main definitions

* `run` — the output of a run from a word, stepped until it halts.
* `expected` — the recognizer's value on a word.

## Main statements

The run halts within the machine's step bound and its output on each word is
the recognizer's value there: `[true]` on an encoding, `[]` otherwise.

## Tags

non-size-increasing, Turing machine, compilation, recognizer
-/

set_option linter.privateModule false

open Geb.SizeBounded Geb.SizeBounded.Machine Turing MultiTapeTM

/-- The machine's output on a word, run to its halt within its step bound, by the
transition function of the machine's program from its initial state. -/
def run (w : List Bool) : Option (List Bool) :=
  stepUntilHalt (machineProg isBitTree).tr (time isBitTree w.length + 1)
    (ExecCfg.init (machineProg isBitTree).q₀ w) []

/-- The recognizer's value on a word. -/
def expected (w : List Bool) : Option (List Bool) :=
  some (if Geb.BitTree.validBool w then [true] else [])

-- Zero fuel cannot observe a halt; positive fuel returns the reversed
-- accumulator immediately, including when most of the budget is unused.
#guard [0, 1, 1000000].all fun fuel ↦
  stepUntilHalt (machineProg isBitTree).tr fuel
    { ExecCfg.init (machineProg isBitTree).q₀ [] with state := none }
    [true, false] == if fuel == 0 then none else some [false, true]

#guard stepUntilHalt (machineProg isBitTree).tr 1 (ExecCfg.init (machineProg isBitTree).q₀ []) []
  = none

#guard run [false, false] = expected [false, false]
#guard run [false, true, true, false] = expected [false, true, true, false]
#guard run [true, false, false, false, false] = expected [true, false, false, false, false]
#guard run [] = expected []
#guard run [true] = expected [true]
#guard run [true, false, false] = expected [true, false, false]
#guard run [false, false, false, false] = expected [false, false, false, false]
#guard run [true, true, true] = expected [true, true, true]
