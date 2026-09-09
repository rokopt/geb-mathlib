/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Cost
public import Geb.Prototypes.Computability.BitTreeScanner.Machine

/-!
# The one-pass tree scanner's output against `validBool`

`bitTreeScanner`'s output on a short list of words, checked against
`Geb.BitTreeScanner.validBool` by kernel evaluation, each run for the steps the
cost model assigns it.

## Main definitions

* `sampleWords` — the words the mirror checks.
* `sampleOutputs` — the scanner's output on each sample word.

## Main statements

* `sampleOutputs_eq` — the scanner emits the decision function's value on
  each sample word.
* `time_sampleWords` — the cost model's steps on each sample word, within the
  bound.

## Implementation notes

The module is admitted to `GebMeta.classicalAllowedModules`. Measurement
(`#print axioms`) finds `sampleWords` axiom-free but `sampleOutputs` and
`sampleOutputs_eq` depending on `Classical.choice`: the taint enters
through `bitTreeScanner.outputString`, which reads the input via
`Turing.MultiTapeTM.Cfg.inputSymbol`, the same root
`Geb/Prototypes/Computability/BitTreeScanner/Steps.lean`'s implementation
notes name for that module's `Classical.choice` dependency. The module has no
choice-free content of its own left to state: its subject is the
correspondence between `bitTreeScanner` and Cslib's
`Turing.MultiTapeTM.outputString`, and `sampleWords` is packaging, the
literal the other declarations are stated over.

## Tags

Turing machine, tree, Elias gamma code, test
-/

@[expose] public section

open Geb.BitTreeScanner Turing MultiTapeTM

namespace BitTreeScannerTest

/-- The words the mirror checks: the empty word, the empty leaf, a leaf of two
bits, a pair of two empty leaves, a pair of a leaf of one bit and an empty
leaf, a leaf of four bits, and three words that spell no tree. -/
def sampleWords : List (List Bool) :=
  [[], [false, true], [false, false, true, true, true, false],
   [true, false, true, false, true], [true, false, false, true, false, true, false, true],
   [false, false, false, true, false, true, true, true, true, true],
   [false, false, true], [true, false, true], [false, true, false]]

/-- The scanner's output on each sample word, over the steps the cost model
assigns it. -/
def sampleOutputs : List (List (Fin 4)) :=
  sampleWords.map fun w ↦
    bitTreeScanner.outputString (bitTreeScanner.initCfg (w.map boolEmb))
      (time w + endCost (scanFinal w))

/-- The scanner emits the decision function's value on each sample word. -/
theorem sampleOutputs_eq :
    sampleOutputs = sampleWords.map fun w ↦ [boolEmb (validBool w)] := by
  decide

/-- The cost model's steps on each sample word, with the steps to the halt. -/
theorem time_sampleWords :
    sampleWords.map (fun w ↦ time w + endCost (scanFinal w)) =
      [1, 10, 20, 20, 28, 32, 4, 11, 11] := by
  decide

end BitTreeScannerTest
