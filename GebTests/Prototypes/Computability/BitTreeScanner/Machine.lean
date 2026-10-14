/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Cost
public import Geb.Prototypes.Computability.BitTreeScanner.Machine
public import Geb.Prototypes.Computability.MultiTape.OfTr
public import Geb.Prototypes.Computability.MultiTape.OutputString

/-!
# The two-pass tree scanner's output against `validBool`

`bitTreeScanner`'s output on a short list of words, checked against
`Geb.BitTreeScanner.validBool` by kernel evaluation, each run for the steps
`Geb.BitTreeScanner.totalTime` assigns it, and halted exactly then.

## Main definitions

* `sampleWords` — the words the mirror checks.
* `sampleRun` — a run of the scanner's transition function on a sample
  word.
* `sampleOutputs` — the output tape of that run on each sample word, over
  the assigned steps.

## Main statements

* `runFrom_eq_sampleRun` — the scanner's run is the run of its transition
  function.
* `sampleOutputs_eq` — the run emits the decision function's value on each
  sample word.
* `halted_sampleRun` — the run has halted at the assigned steps and not one
  step before.
* `outputString_sampleWords` — the scanner emits the decision function's
  value on each sample word.
* `halted_sampleWords` — the scanner has halted at the assigned steps and
  not one step before.
* `totalTime_sampleWords` — the assigned steps on each sample word.
* `totalTime_le_sampleWords` — the assigned steps within the bound.

## Implementation notes

The module is admitted to `GebMeta.classicalAllowedModules`. Its subject is
the correspondence between `bitTreeScanner` and the output emitted along a
run of Cslib's `Turing.MultiTapeTM.runFrom`
(`Turing.MultiTapeTM.outputString`), which reads the input via
`Turing.Cfg.inputSymbol`, the root
`Geb/Prototypes/Computability/BitTreeScanner/Steps/Basic.lean`'s
implementation notes name for that module's `Classical.choice` dependency;
`sampleWords` is packaging, the literal the other declarations are stated
over.

Cslib's step of a machine is chosen from its transition relation and does
not reduce, so the kernel evaluates the run of `transition` by
`Turing.MultiTapeTM.stepOfTr`, and `Turing.MultiTapeTM.runFrom_ofTr`
identifies that run with the scanner's.

## Tags

Turing machine, tree, Elias gamma code, two passes, test
-/

@[expose] public section

open Geb.BitTreeScanner Turing MultiTapeTM

namespace BitTreeScannerTest

/-- The words the mirror checks: the empty word, the empty leaf, a leaf of two
bits, a pair of two empty leaves, a pair of a leaf of one bit and an empty
leaf, a leaf of four bits, three pairs over four empty leaves, whose pending
count carries and borrows through a zero, and four words that spell no tree:
a leaf cut short, a pair cut short, a bit after completion, and a gamma code
with more zeros than the word's bound. -/
def sampleWords : List (List Bool) :=
  [[], [false, true], [false, false, true, true, true, false],
   [true, false, true, false, true], [true, false, false, true, false, true, false, true],
   [false, false, false, true, false, true, true, true, true, true],
   [true, true, true, false, true, false, true, false, true, false, true],
   [false, false, true], [true, false, true], [true, false, true, false, true, true],
   [false, false, false, false, false, false]]

/-- The configuration after `n` steps of the scanner's transition function
from the initial configuration on a word. -/
def sampleRun (w : List Bool) (n : ℕ) : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb) :=
  (stepOfTr transition)^[n] (Cfg.init stInit (w.map boolEmb))

/-- The scanner's run from the initial configuration is the run of its
transition function. -/
theorem runFrom_eq_sampleRun (w : List Bool) (n : ℕ) :
    bitTreeScanner.runFrom (bitTreeScanner.initCfg (w.map boolEmb)) n = sampleRun w n := by
  rw [bitTreeScanner, runFrom_ofTr]
  rfl

/-- The output tape of the run on each sample word, over the assigned
steps. -/
def sampleOutputs : List (List (Fin 4)) :=
  sampleWords.map fun w ↦ (sampleRun w (totalTime w)).output

/-- The run emits the decision function's value on each sample word. -/
theorem sampleOutputs_eq :
    sampleOutputs = sampleWords.map fun w ↦ [boolEmb (validBool w)] := by
  decide +kernel

/-- The run has halted at the assigned steps, and had not one step before. -/
theorem halted_sampleRun :
    sampleWords.map (fun w ↦
      (decide ((sampleRun w (totalTime w)).state = none),
        decide ((sampleRun w (totalTime w - 1)).state = none))) =
      sampleWords.map fun _ ↦ (true, false) := by
  decide +kernel

/-- The scanner emits the decision function's value on each sample word. -/
theorem outputString_sampleWords :
    sampleWords.map (fun w ↦
      bitTreeScanner.outputString (bitTreeScanner.initCfg (w.map boolEmb)) (totalTime w)) =
      sampleWords.map fun w ↦ [boolEmb (validBool w)] := by
  simp only [← initCfg_runFrom_output, runFrom_eq_sampleRun]
  exact sampleOutputs_eq

/-- The scanner has halted at the assigned steps, and had not one step
before. -/
theorem halted_sampleWords :
    sampleWords.map (fun w ↦
      (decide ((bitTreeScanner.runFrom (bitTreeScanner.initCfg (w.map boolEmb))
          (totalTime w)).state = none),
        decide ((bitTreeScanner.runFrom (bitTreeScanner.initCfg (w.map boolEmb))
          (totalTime w - 1)).state = none))) =
      sampleWords.map fun _ ↦ (true, false) := by
  simp only [runFrom_eq_sampleRun]
  exact halted_sampleRun

/-- The assigned steps on each sample word. -/
theorem totalTime_sampleWords :
    sampleWords.map totalTime = [4, 20, 46, 44, 68, 76, 100, 16, 26, 50, 33] := by
  decide

/-- The assigned steps on each sample word are within the bound. -/
theorem totalTime_le_sampleWords :
    sampleWords.all (fun w ↦ decide (totalTime w ≤ 14 * w.length + 4)) = true := by
  decide

end BitTreeScannerTest
